################## Diversity analysis North East Atlantic ################
## Created by Nestor E. Bosch on 13th July 2020
## Please report any bug to nbosch1989@gmail.com

## Index
## (1) Map on spatial extent of the study 
## (2) Calculate TD 
## (3) Calculate FD 
## (4) Calculate PD
## (5) Download LDG drivers
## (6) GAMs on LDG in TD, FD and PD
## (7) RElative importance of assembly mechanisms
## (8) LMs for testing LDG hypothesis
## (9) Model-averaged coefficients
## (10) Demographic stochasticity

## Clean the working directory

rm(list=ls())

## Load libraries

library(dplyr)
library(tidyr)
library(stringr)
library(ggplot2)
library(gridExtra)
library(data.table)
library(sp)
library(rgdal)
library(rgeos)
library(maptools)
library(broom)
library(ape)
library(geosphere)
library(ggpubr)
library(FD)

# Theme-
Theme1 <-
  theme( # use theme_get() to see available options
    panel.grid.major = element_blank(), 
    panel.grid.minor = element_blank(), 
    # legend.background = element_rect(fill="white"),
    legend.background = element_blank(),
    legend.key = element_blank(), # switch off the rectangle around symbols in the legend
    legend.text = element_text(size=10),
    legend.title = element_blank(),
    legend.position = c(0.2, 0.8),
    text=element_text(size=14),
    strip.text.y = element_text(size = 14,angle = 0),
    axis.title.x=element_text(vjust=0.3, size=12),
    axis.title.y=element_text(vjust=0.6, angle=90, size=12),
    axis.text.x=element_text(size=10),
    axis.text.y=element_text(size=10),
    axis.line.x=element_line(colour="black", size=0.5,linetype='solid'),
    axis.line.y=element_line(colour="black", size=0.5,linetype='solid'),
    strip.background = element_blank())

## Functional alpha diversity for a set of N assemblages from Chao et al. 2019 ----

FD_MLE <- function(data, dij, tau, q){
  dij <- as.matrix(dij)
  dij[which(dij>tau,arr.ind = T)] <- tau
  a <- as.vector((1 - dij/tau) %*% data )  
  data <- data[a!=0]
  a <- a[a!=0]
  v <- data/a
  nplus <- sum(data)
  if(q==1){
    exp(sum(-v*a/nplus*log(a/nplus)))
  }else{
    (sum(v*(a/nplus)^q))^(1 / (1-q))
  }
}

FunD <- function(data, dij, tau, q, boot, datatype){
  EstiBootComm.Func = function(data, distance, datatype){
    if (datatype=="abundance") {
      n = sum(data)
    } else if (datatype=="incidence_raw") {
      n <- data[1]
      data <- data[-1]
      u=sum(data)
    }
    distance = as.matrix(distance)
    dij = distance[data!=0, data!=0]
    
    X = data[data>0]
    f1 <- sum(X == 1) ; f2 <- sum(X == 2) 	
    f0.hat <- ceiling(ifelse(f2>0, ((n-1)/n)*f1^2/2/f2, ((n-1)/n)*f1*(f1-1)/2))
    if (datatype=="abundance") {
      C1 = ifelse(f2>0, 1-f1*(n-1)*f1/n/((n-1)*f1+2*f2), 1-f1*(n-1)*(f1-1)/n/((n-1)*(f1-1)+2))
      W <- (1 - C1)/sum(X/n*(1-X/n)^n) 
      Prob.hat.Unse <- rep((1-C1)/f0.hat, f0.hat)
    } else if (datatype=="incidence_raw") {
      C1 = ifelse(f2>0, 1-f1/u*(n-1)*f1/((n-1)*f1+2*f2), 1-f1*(n-1)*(f1-1)/u/((n-1)*(f1-1)+2))
      W <- (1 - C1)/sum(X/u*(1-X/n)^n) 
      Prob.hat.Unse <- rep(u/n*(1-C1)/f0.hat, f0.hat)	
    }
    
    Prob.hat <- X/n*(1-W*(1-X/n)^n)
    Prob <- c(Prob.hat, Prob.hat.Unse)
    
    F.1 <- sum(dij[, X==1]) ; F.2 <- sum(dij[, X==2])
    F11 <- sum(dij[X==1, X==1]) ; F22 <- sum(dij[X==2, X==2])
    #
    if (datatype=="abundance") {
      F.0hat <- ifelse(F.2 > 0, ((n-1)/n) * (F.1^2/(2 * F.2)), ((n-1)/n)*(F.1*(F.1-0.01)/(2)))
      F00hat <- ifelse(F22 > 0, ((n-2)* (n-3)* (F11^2)/(4* n* (n-1)* F22)), ((n-2)* (n-3)* (F11*(F11-0.01))/(4 *n * (n-1))) )
    } else if (datatype=="incidence_raw") {
      F.0hat <- ifelse(F.2 > 0, ((n-1)/n) * (F.1^2/(2 * F.2)), ((n-1)/n)*(F.1*(F.1-0.01)/(2)))
      F00hat <- ifelse(F22 > 0, ((n-1)^2 * (F11^2)/(4* n* n* F22)), ((n-1)* (n-1)* (F11*(F11-0.01))/(4 *n * n)) )
    }
    if (f0.hat==0) {
      d=dij
    } else if (f0.hat==1) {
      random_dij = as.vector(rmultinom(1, 1000, rep(1/(length(X)*f0.hat), length(X)*f0.hat) ) )/1000
      d.0bar <- matrix(random_dij*F.0hat, length(X), f0.hat, byrow = T)
      d00 = matrix(0, f0.hat, f0.hat)
      d <- cbind(dij, d.0bar )
      aa <- cbind(t(d.0bar), d00 )
      d <- rbind(d, aa)
      diag(d) = 0
    } else {
      random_dij = as.vector(rmultinom(1, 1000, rep(1/(length(X)*f0.hat), length(X)*f0.hat) ) )/1000
      d.0bar <- matrix(random_dij*F.0hat, length(X), f0.hat, byrow = T)
      
      fo.num = (f0.hat * (f0.hat-1) )/2
      random_d00 = as.vector(rmultinom(1, 1000, rep(1/fo.num, fo.num) ) )/1000
      d00 = matrix(0, f0.hat, f0.hat)
      d00[upper.tri(d00)] = (F00hat/2)*random_d00
      d00 <- pmax(d00, t(d00))###signmatrix
      d <- cbind(dij, d.0bar )
      aa <- cbind(t(d.0bar), d00 )
      d <- rbind(d, aa)
      diag(d) = 0
    }
    return(list("pi" = Prob,"dij" = d))
  }
  dij <-  as.matrix(dij)
  out <- as.vector(dij)
  out <- out[out!=0]
  dmin <- min(out)
  dmax <- max(out)
  if (datatype=="incidence_raw") {
    data <- lapply(data, function(i) {
      c(ncol(i), rowSums(i))
    })
  }
  if (datatype=="abundance") {
    if(length(data)!=1){
      tmp <- apply(do.call(cbind,lapply(data, FUN = function(x) x/sum(x))), 1, mean)
      dmean <-  sum ( (tmp %*% t(tmp) ) * dij) 
    }else{
      tmp <- data[[1]]/sum(data[[1]])
      dmean <-  sum ( (tmp %*% t(tmp) ) * dij)   
    }
  } else {
    if(length(data)!=1){
      tmp <- apply(do.call(cbind,lapply(data, FUN = function(x) x[-1]/sum(x[-1]))), 1, mean)
      dmean <-  sum ( (tmp %*% t(tmp) ) * dij) 
    }else{
      tmp <- data[[1]][-1]/sum(data[[1]][-1])
      dmean <-  sum ( (tmp %*% t(tmp) ) * dij)   
    }
  }
  FD.CI = function(data, dij, tau, q, datatype){
    if (datatype == "abundance") {
      qFun = FD_MLE(data, dij, tau, q)
    } else {
      qFun = FD_MLE(data[-1], dij, tau, q)
    }
    if(boot!=0){
      BT = EstiBootComm.Func(data, dij, datatype)
      p_hat = BT[[1]]
      dij_boot = BT[[2]]
      dij_boot <-  as.matrix(dij_boot)
      dij_boot <- replace(dij_boot, dij_boot==0, 10^(-10))
      for (i in seq_len(nrow(dij_boot))) {
        dij_boot[i, i] <- 0
      }
      if (datatype=="abundance") {
        n=sum(data)
        Boot.X = rmultinom(boot, n, p_hat)
      } else {
        n=data[1]
        Boot.X = t(sapply(p_hat,function(i) rbinom(boot, n, i)))
      }
      qFun_sd = sd(sapply(seq_len(ncol(Boot.X)), function(i) {
        FD_MLE(Boot.X[, i], dij_boot, tau, q)
      }))
    }else{
      qFun_sd = 0
    }
    LCL = max(0, qFun - qnorm(0.975) * qFun_sd)
    UCL = qFun + qnorm(0.975) * qFun_sd
    a = round(c(qFun, qFun_sd, LCL, UCL), 4)
    a
  }
  
  Funq <- function(data, datatype){
    dminFDforq <- t(sapply(q, FUN = function(q) FD.CI(data, dij, dmin, q, datatype) ))
    dmaxFDforq <- t(sapply(q, FUN = function(q) FD.CI(data, dij, dmax, q, datatype) ))
    dmeanFDforq <-t(sapply(q, FUN = function(q) FD.CI(data, dij, dmean, q, datatype) ))
    out <- data.frame(rep(q,3), rbind(dminFDforq,dmaxFDforq,dmeanFDforq),rep(c("dmin","dmax","dmean"),each=length(q)))
  }
  Funtau <- function(data, datatype){
    q0FDfortau <- t(sapply(tau, FUN = function(tau) FD.CI(data, dij, tau, 0, datatype) ))
    q1FDfortau <- t(sapply(tau, FUN = function(tau) FD.CI(data, dij, tau, 1, datatype) ))
    q2FDfortau <- t(sapply(tau, FUN = function(tau) FD.CI(data, dij, tau, 2, datatype) ))
    out <- data.frame(rep(tau,3), rbind(q0FDfortau,q1FDfortau,q2FDfortau),rep(c("0","1","2"),each=length(tau)))
  }
  
  if(length(data)!=1){
    name = names(data)
    Outputforq <- data.frame(do.call(rbind,lapply(data, Funq, datatype=datatype)), rep(name, each=3*length(q)), row.names = NULL)
    Outputfortau <- data.frame(do.call(rbind,lapply(data, Funtau, datatype=datatype)), rep(name, each=3*length(tau)), row.names = NULL)
  }else{
    name = names(data)
    Outputforq <- data.frame(Funq(data[[1]], datatype), name, row.names = NULL)
    Outputfortau <- data.frame(Funtau(data[[1]], datatype), name, row.names = NULL)
  }
  colnames(Outputforq) <- c("q","estimate", "s.e.", "LCL", "UCL", "tau","site")
  colnames(Outputfortau) <- c("tau","estimate", "s.e.", "LCL", "UCL", "q","site")
  
  Output <- list(forq = Outputforq, fortau = Outputfortau)
  return(Output)
}

#######################################################################################################
##################### (1) Map on the spatial extent of the study ######################################

## Read in NEA_analyses dataset

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Raw')
dir()

dat<-read.csv("NEA_analyses.csv")%>%
  glimpse()

## Get quick summaries for text

n_distinct(dat$Site)
n_distinct(dat$Ecoregion)
mean(dat$Depth)
sd(dat$Depth)
range(dat$Year)
mean(dat$Year)
sd(dat$Year)
n_distinct(dat$Taxa)
n_distinct(dat$GENUS)
n_distinct(dat$FAMILY)
n_distinct(dat$ORDER)

## Summary for supplementary data of eastern Atlantic dataset

test<-dat%>%
  filter(Dimensions<500)%>%
  group_by(Ecoregion,Location,Site,Latitude,Longitude)%>%
  summarise(Year=first(Year),
            Total_Effort=mean(Effort),
            Dimensions=first(Dimensions),
            Total_Area=Dimensions*Total_Effort,
            Depth_min=min(Depth),
            Depth_max=max(Depth),
            Depth_mean=mean(Depth),
            Depth_sd=sd(Depth),
            Richness=n_distinct(Taxa))%>%
  glimpse()
  
## Export summary table

write.csv(test,"Atlantic.dataset.csv")

## Load libraries

library(rgdal)
library(scales)
library(raster)
library(iNEXT)
library(forcats)

## Clean the working directory

rm(atlantic.data.pooled,rls.data.pooled,atlantic,NEA.analyses,test)

## Bring in Atlantic shapefile

setwd("C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Shapefiles/North-Atlantic")
dir()

atlantic<-readOGR('.','ne_50m_ocean')
proj4string(atlantic)
plot(atlantic)

## Crop the extent to the eastern Atlantic dataset

e<-extent(-32,20,-24,90,-35)
atlantic<-crop(atlantic,e)
plot(atlantic)

## Convert into a dataframe

atlantic<-fortify(atlantic)

## Bring in Land shapefile

setwd("C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Shapefiles/Land")
dir()

land<-readOGR('.','ne_10m_land')
proj4string(land)
plot(land)

## Crop the extent to the eastern Atlantic dataset

e<-extent(-32,20,-24,90,-35)
land<-crop(land,e)
plot(land)

## Convert into a dataframe

land<-fortify(land)

## Create a summary data for plotting

glimpse(NEA.analyses)

dat.summary<-dat%>%
  group_by(Ecoregion,Site)%>%
  summarise(Latitude=mean(Latitude,na.rm=T),
            Longitude=mean(Longitude,na.rm=T),
            Source=first(Source))%>%
  ungroup()%>%
  glimpse()
unique(dat.summary$Ecoregion)
n_distinct(dat.summary$Site) ## 279 Sites

## Create summary of sites by Ecoregion

ecoregion.summary<-dat%>%
  group_by(Ecoregion)%>%
  summarise(N=n_distinct(Site),
            S=n_distinct(Taxa))%>%
  glimpse()

## Reorder levels of the factor

dat.summary<-dat.summary%>%
  mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

## Plot map of spatial extent of the study

map.points<-ggplot()+
  geom_polygon(data=land,aes(x=long,y=lat,group=group),fill="gray12",alpha=0.5,colour="black",linetype="solid",size=0.3)+
  geom_point(data=dat.summary,aes(x=Longitude,y=Latitude,fill=Ecoregion,shape=Ecoregion),
             position = position_jitter(h=0.5, w=0.5),size=2.5,show.legend=T)+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                 "South European Atlantic Shelf","Celtic Seas",
                                 "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  coord_equal()+
  scale_y_continuous(breaks = c(-20,0,20,40,60,80),expand = c(0,0))+
  scale_x_continuous(expand = c(0,0))+
  xlab('Longitude (°)')+
  ylab('Latitude (°)')+
  ggtitle('')+
  theme_classic()+
  Theme1+
  theme(legend.position = "right",
        legend.text = element_text(size=12),
        legend.key.width = unit(0.5, "cm"))
map.points

##### Export plots

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/Study region')
dir()

name<-'eastern.Atlantic'

ggsave(paste(name,"map.png",sep="."),width = 21, height = 15,units = "cm",dpi=300,scale=2)
ggsave(paste(name,"map.pdf",sep="."),width = 21, height = 15,units = "cm",dpi=300,useDingbats=FALSE)

#######################################################################################################################
########################### (2) Calculate alpha Taxonomic Diversity  ########################################################

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Raw')
dir()

dat<-read.csv("NEA_analyses.csv")%>%
  mutate(Total_area=Dimensions*Effort)%>%
  dplyr::select(-TotalAbun)%>%
  #mutate(response=log1p(response))%>% ## Log transform abundance to balance the contribution of dominant and rare entities
  #filter(!Source%in%c('RLS'))%>% ## Test whether the data source have an effect on the patterns
  glimpse()
n_distinct(dat$Site)
unique(dat$Source)
n_distinct(dat$Taxa)

## Check species abundances distributions

library(forcats)
unique(dat$Ecoregion)

dat<-dat%>%
  dplyr::mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Webbnesia",
                                      "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

ggplot(dat,aes(x=Ecoregion,y=response,colour=Ecoregion))+
  geom_boxplot()+
  theme_classic()+
  Theme1+
  theme(legend.position="bottom")

ggplot(dat%>%filter(response>0),aes(x=reorder(FAMILY,-response),y=response,colour=Ecoregion))+
  geom_boxplot(show.legend = F)+
  facet_wrap(~Ecoregion,scales = "free")+
  theme_classic()+
  Theme1+
  theme(axis.text.x = element_text(angle=90,hjust = 1,vjust=0))

ggplot(dat%>%filter(response>0),aes(x=reorder(Taxa,-response),y=response,colour=Ecoregion))+
  geom_boxplot(show.legend = F)+
  facet_wrap(~Ecoregion,scales = "free")+
  theme_classic()+
  Theme1+
  theme(axis.text.x = element_text(angle=90,hjust = 1,vjust=0))

## Compute Total abundance at a site and join to the diversity analyses dataset

test<-dat%>%
  dplyr::group_by(Ecoregion,Site)%>%
  dplyr::summarise(TotalAbun=sum(response))%>%
  glimpse()

dat<-left_join(dat,test,by=c("Ecoregion","Site"))%>%
  glimpse()

ggplot(dat,aes(x=Ecoregion,y=TotalAbun))+
  geom_bar(stat = "identity")

####### Using a weighthed-information criterion based on Hill numbers of order q 
### Hill numbers = equivalent number of speices (Jost, 2006)

n_distinct(dat$Taxa)
n_distinct(dat$Site)

## Generate species x abundance matrix

glimpse(dat)

Abun<-as.data.frame(dat)%>%
  dplyr::select(Site,Taxa,response)%>%
  pivot_wider(names_from = "Taxa",values_from = response) %>%
  mutate_all(~replace_na(., 0))%>%
  glimpse()

## Set sites as row names

Abun<-data.frame(Abun)
rownames(Abun) <- Abun[,1] #Assigning row names from 1st column 
Abun[,1] <- NULL #Removing the first column

## (A) "q" = 0 ----

### Convert species abundance to incidence data for "q" = 0

mat<-Abun
mat[mat>0] <-1

### Calculating Diversity Indices at the site level based on Hill numbers - using package HillR 

library(hillR)

TD.0<-hill_taxa(mat, q = 0) # Richness
TD.0<-as.data.frame(TD.0)

## Convert row names to a

library(tibble)

colnames(TD.0)<-'TD_q0'
TD.0<-rownames_to_column(TD.0, var = "Site")

## (B) "q" = 1 ----

### Calculating Diversity Indices at the site level based on Hill numbers - using package HillR 

library(hillR)

TD.1<-hill_taxa(Abun, q = 1) # Richness
TD.1<-as.data.frame(TD.1)

## Convert row names to a

library(tibble)

colnames(TD.1)<-'TD_q1'
TD.1<-rownames_to_column(TD.1, var = "Site")

## (C) "q" = 2 ----

### Calculating Diversity Indices at the site level based on Hill numbers - using package HillR

library(hillR)

TD.2<-hill_taxa(Abun, q = 2) # Richness
TD.2<-as.data.frame(TD.2)

## Convert row names to a

library(tibble)

colnames(TD.2)<-'TD_q2'
TD.2<-rownames_to_column(TD.2, var = "Site")

## Create a dataframe for latitudinal diversity analyses

glimpse(dat)

diversity<-dat%>%
  dplyr::group_by(Ecoregion,Site,Latitude,Longitude)%>%
  dplyr::summarise(Total_Abun=first(TotalAbun),
                   Total_area=first(Total_area))%>%
  glimpse()

diversity<-left_join(diversity,TD.0,by="Site")%>%
  glimpse()

diversity<-left_join(diversity,TD.1,by="Site")%>%
  glimpse()

diversity<-left_join(diversity,TD.2,by="Site")%>%
  glimpse()

## Export diversity dataset

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity.25052021.csv")

#################################################################################################################
############################################### (3) Calculate alpha Functional diversity  #############################

## Filter species not present in community data

x<-as.vector(colnames(Abun))

## Bring in corrected traits

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Databases')
dir()

traits<-read.csv("traits.final.csv")%>%
  dplyr::select(-Trophic.group2,-Diel.Activity)%>%
  glimpse()
sum(is.na(traits))
traits$Taxa<-gsub(" ",".",traits$Taxa)

traits<-traits%>%
  filter(Taxa%in%x)%>%
  glimpse()

#Order the traits alphabetically
traits <- traits[order(traits[, 1]), ]

## Make sure there is no replicate levels in the traits

unique(traits$Trophic.group)
unique(traits$Water.column)
unique(traits$Diel.Activity)
unique(traits$Habitat)
unique(traits$Gregariousness)

# Code traits

traits<-traits%>%
  mutate(MaxLength=cut(MaxLength,breaks = c(-Inf,10,15,30,50,80,Inf),
                       labels = c("Very small","Small","Medium",
                                  "Large","Very large","Super large")))%>%
  glimpse()

traits$Trophic.group <- as.factor(traits$Trophic.group)

traits$Water.column <- as.factor(traits$Water.column)

traits$Diel.Activity <- as.factor(traits$Diel.Activity)

traits$Habitat <- as.factor(traits$Habitat)

traits$Gregariousness <- ordered(traits$Gregariousness, levels = c("1", "2", "3"))

glimpse(traits)

## Set species as row names in the trait matrix

rownames(traits) <- traits[,1] #Assigning row names from 1st column 
traits[,1] <- NULL #Removing the first column

### Subset community matrix to only species with traits

x<-as.vector(rownames(traits))

## Organize species in the community matrix in the same order as in the trait matrix

Abun<-Abun[,order(colnames(Abun))]

## Remove species with no traits

Abun<-Abun[,x]

## (A.1) Calculate SES Functional Attribute Diversity
## Using and independent swap algorith from a regional pool define by all the species samples in the NEA Atlantic
## Problems with convex hulls for community with low species richness
## Use the new proposed metric of Functional attribute diversity - Chao et al. 2019
## Based on generalization of Hill numbers with parameter t - mean functional distances between species

## (A) "q" = 0 ----

## (A.1) Observed FD_q0

## Calculate multitrait dissimilarities

library(gawdis)

gowmat<-as.matrix(gawdis(traits, w.type ="equal"))

## First - because "q" = 0 still is dependent of species abundance - we will convert this to incidence data

mat<-Abun
mat[mat>0] <-1

## Convert abundances to a list of N sites with abundances as vectors

mat<-as.matrix(mat)
mat<-t(mat)

## Compute Observed FD ("q" = 0)

## Create a list of repetition of communities

number<-seq(1,279,1)
list<-as.list(number)

## Create an empty dataframe to store the results

dataframe=data.frame()

for (number in list){
  
  result<-as.data.frame(FD_MLE(mat[,number], gowmat, mean(gowmat), 0))
  
  dataframe<-rbind(dataframe,result)
  
}

colnames(dataframe)<-'FD_q0'
dataframe$Site<-colnames(mat)
FD.0<-dataframe

## (A.1.2) Null FD 

## Now we need to randomize the community matrix from the global pool of species 

mat<-t(mat) ## Reorganize community data matrix as original - i.e. species as columns

library(picante)

dataframe.1=data.frame()
iteration=1:999

for(i in iteration) {
  
  reps = as.matrix(randomizeMatrix(mat, null.model = "independentswap"))
  reps<-t(reps)
  
  ## Create a list of repetition of communities
  
  number<-seq(1,279,1)
  list<-as.list(number)
  
  ## Create an empty dataframe to store the results
  
  dataframe=data.frame()
  
  for (number in list){
    
    result<-as.data.frame(FD_MLE(reps[,number], gowmat, mean(gowmat), 0))
    
    dataframe<-rbind(dataframe,result)
    
  }
  
  colnames(dataframe)<-'FD_q0'
  dataframe$Site<-colnames(reps)
  dataframe.1<-rbind(dataframe.1,dataframe)
  
}

## Calculate Mean and SD of the null community

summary<-dataframe.1%>%
  dplyr::group_by(Site)%>%
  dplyr::summarise(Mean_FD_q0=mean(FD_q0,na.rm = TRUE),
                   Sd_FD_q0=sd(FD_q0))%>%
  glimpse()

## Calculate SES FD (Rao Q)
## (SES = (obs - mean(null))/sd(null))

FD.0<-left_join(FD.0,summary,by=c("Site"))%>%glimpse()

FD.0<-FD.0%>%
  mutate(SES.FD_q0 = (FD_q0 - Mean_FD_q0)/Sd_FD_q0)%>%
  select(Site,FD_q0,SES.FD_q0)%>%
  glimpse()

## Calculate percetiles on the null distribution and classified communities: underdispersed (<5th), overdispersed (>95th) or random

quantile(dataframe.1$FD_q0, c(.05,0.25,0.75,0.95)) 

FD.0<-FD.0%>%
  mutate(p.FD.q0=ifelse(FD_q0<=1.556994,"Underdispersed (95%)",
                        ifelse(FD_q0<=2.387950,"Underdispersed (75%)",
                               ifelse(FD_q0>=5.232257,"Overdispersed (95%)",
                                      ifelse(FD_q0>=3.927308,"Overdispersed (75%)","Random")))))%>%
  glimpse()

## (B) "q" = 1 ----

## (A.1) Observed FD_q1

## Calculate multitrait dissimilarities

library(gawdis)

gowmat<-as.matrix(gawdis(traits, w.type ="equal"))

## First - because "q" = 0 still is dependent of species abundance - we will convert this to incidence data

mat<-Abun

## Convert abundances to a list of N sites with abundances as vectors

mat<-as.matrix(mat)
mat<-t(mat)

## Compute Observed FD ("q" = 1)

## Create a list of repetition of communities

number<-seq(1,279,1)
list<-as.list(number)

## Create an empty dataframe to store the results

dataframe=data.frame()

for (number in list){
  
  result<-as.data.frame(FD_MLE(mat[,number], gowmat, mean(gowmat), 1))
  
  dataframe<-rbind(dataframe,result)
  
}

colnames(dataframe)<-'FD_q1'
dataframe$Site<-colnames(mat)
FD.1<-dataframe

## (A.1.2) Null FD 

## Now we need to randomize the community matrix from the global pool of species 

mat<-t(mat) ## Reorganize community data matrix as original - i.e. species as columns

library(picante)

dataframe.1=data.frame()
iteration=1:999

for(i in iteration) {
  
  reps = as.matrix(randomizeMatrix(mat, null.model = "independentswap"))
  reps<-t(reps)
  
  ## Create a list of repetition of communities
  
  number<-seq(1,279,1)
  list<-as.list(number)
  
  ## Create an empty dataframe to store the results
  
  dataframe=data.frame()
  
  for (number in list){
    
    result<-as.data.frame(FD_MLE(reps[,number], gowmat, mean(gowmat), 1))
    
    dataframe<-rbind(dataframe,result)
    
  }
  
  colnames(dataframe)<-'FD_q1'
  dataframe$Site<-colnames(reps)
  dataframe.1<-rbind(dataframe.1,dataframe)
  
}

## Calculate Mean and SD of the null community

summary<-dataframe.1%>%
  dplyr::group_by(Site)%>%
  dplyr::summarise(Mean_FD_q1=mean(FD_q1,na.rm = TRUE),
                   Sd_FD_q1=sd(FD_q1))%>%
  glimpse()

## Calculate SES FD (Rao Q)
## (SES = (obs - mean(null))/sd(null))

FD.1<-left_join(FD.1,summary,by=c("Site"))%>%glimpse()

FD.1<-FD.1%>%
  mutate(SES.FD_q1 = (FD_q1 - Mean_FD_q1)/Sd_FD_q1)%>%
  select(Site,FD_q1,SES.FD_q1)%>%
  glimpse()

## Calculate percetiles on the null distribution and classified communities: underdispersed (<5th), overdispersed (>95th) or random

quantile(dataframe.1$FD_q1, c(.05,0.25,0.75,0.95)) 

FD.1<-FD.1%>%
  mutate(p.FD.q1=ifelse(FD_q1<=1.103698,"Underdispersed (95%)",
                        ifelse(FD_q1<=1.447509,"Underdispersed (75%)",
                               ifelse(FD_q1>=2.352702,"Overdispersed (75%)",
                                      ifelse(FD_q1>=3.273992,"Overdispersed (95%)","Random")))))%>%
  glimpse()

## (C) "q" = 2 ----

## (A.1) Observed FD

## Calculate multitrait dissimilarities

library(gawdis)

gowmat<-as.matrix(gawdis(traits, w.type ="equal"))

## First - because "q" = 0 still is dependent of species abundance - we will convert this to incidence data

mat<-Abun

## Convert abundances to a list of N sites with abundances as vectors

mat<-as.matrix(mat)
mat<-t(mat)

## Compute Observed FD ("q" = 2)

## Create a list of repetition of communities

number<-seq(1,279,1)
list<-as.list(number)

## Create an empty dataframe to store the results

dataframe=data.frame()

for (number in list){
  
  result<-as.data.frame(FD_MLE(mat[,number], gowmat, mean(gowmat), 2))
  
  dataframe<-rbind(dataframe,result)
  
}

colnames(dataframe)<-'FD_q2'
dataframe$Site<-colnames(mat)
FD.2<-dataframe

## (A.1.2) Null FD 

## Now we need to randomize the community matrix from the global pool of species 

mat<-t(mat) ## Reorganize community data matrix as original - i.e. species as columns

library(picante)

dataframe.1=data.frame()
iteration=1:999

for(i in iteration) {
  
  reps = as.matrix(randomizeMatrix(mat, null.model = "independentswap"))
  reps<-t(reps)
  
  ## Create a list of repetition of communities
  
  number<-seq(1,279,1)
  list<-as.list(number)
  
  ## Create an empty dataframe to store the results
  
  dataframe=data.frame()
  
  for (number in list){
    
    result<-as.data.frame(FD_MLE(reps[,number], gowmat, mean(gowmat), 2))
    
    dataframe<-rbind(dataframe,result)
    
  }
  
  colnames(dataframe)<-'FD_q2'
  dataframe$Site<-colnames(reps)
  dataframe.1<-rbind(dataframe.1,dataframe)
  
}

## Calculate Mean and SD of the null community

summary<-dataframe.1%>%
  dplyr::group_by(Site)%>%
  dplyr::summarise(Mean_FD_q2=mean(FD_q2,na.rm = TRUE),
                   Sd_FD_q2=sd(FD_q2))%>%
  glimpse()

## Calculate SES FD (Rao Q)
## (SES = (obs - mean(null))/sd(null))

FD.2<-left_join(FD.2,summary,by=c("Site"))%>%glimpse()

FD.2<-FD.2%>%
  mutate(SES.FD_q2 = (FD_q2 - Mean_FD_q2)/Sd_FD_q2)%>%
  select(Site,FD_q2,SES.FD_q2)%>%
  glimpse()

## Calculate percetiles on the null distribution and classified communities: underdispersed (<5th), overdispersed (>95th) or random

quantile(dataframe.1$FD_q2, c(.05,0.25,0.75,0.95)) 

FD.2<-FD.2%>%
  mutate(p.FD.q2=ifelse(FD_q2<=1.069777,"Underdispersed (95%)",
                        ifelse(FD_q2<=1.345317,"Underdispersed (75%)",
                               ifelse(FD_q2>=2.147895,"Overdispersed (75%)",
                                      ifelse(FD_q2>=2.994611,"Overdispersed (95%)","Random")))))%>%
  glimpse()

## Join datasets with original diversity metrics and export

diversity<-left_join(diversity,FD.0,by="Site")%>%glimpse()
diversity<-left_join(diversity,FD.1,by="Site")%>%glimpse()
diversity<-left_join(diversity,FD.2,by="Site")%>%glimpse()

## Export 

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity.25052021.csv")

##############################################################################################################################
######################################### (4) Calculate alpha Phylogenetic diversity ###############################################

### Bring in species list from trait matrix

### Download phylogenetic tree from FishTree package
### For now only 1158 species are found out of 1726 - that close to 32% of the species will need to tackle this later on

## Need to correct species names in the community by replacing space for _

n_distinct(dat$Taxa)
ncol(Abun)
nrow(Abun)

species<-as.vector(colnames(Abun))
species<-gsub('\\.','_',species)

## Load the R package fishtree

library(fishtree)

phy <- fishtree_complete_phylogeny(species) ## 19 species missing - the majority species not identify to species level 
phy <- phy[[1]] 
phy$tip.label <- gsub("_", ".", phy$tip.label)
phy$tip.label

#Convert tree into ultrametric distance matrix

phylo.dist <- as.matrix(cophenetic(phy))

phylo.dist <- phylo.dist/max(phylo.dist)

min(phylo.dist)
max(phylo.dist)

## Mantel test for correlation between phylogenetic and trait distances - i.e. Phylogenetic signal

library(vegan)

x<-rownames(phylo.dist)

gowmat<-gowmat[x,x]

mantel(phylo.dist, gowmat, method="pearson", permutations=999) # Correlation between matrix of traits and phylogenies. To see if the traits are conserved


### Plot the tree and export for the supplementary materials - not necessary for now

#plot.phylo(phy, type="fan", show.tip.label=TRUE, font = 4, cex=0.5, edge.color="blue", edge.width= 2, tip.color="black") 

### Prune species missing in the phylogenetic tree from community data

x<-phy$tip.label

Abun<-Abun[,x]

## (A.1) Calculate SES Phylogenetic Attribute Diversity
## Using and independent swap algorith from a regional pool define by all the species samples in the NEA Atlantic
## Problems with convex hulls for community with low species richness
## Use the new proposed metric of Functional attribute diversity - Chao et al. 2019
## Based on generalization of Hill numbers with parameter t - mean functional distances between species

## (A) "q" = 0 ----

## (A.1) Observed PD

## Calculate multitrait dissimilarities

## First - because "q" = 0 still is dependent of species abundance - we will convert this to incidence data

mat<-Abun
mat[mat>0] <-1

## Convert abundances to a list of N sites with abundances as vectors

mat<-as.matrix(mat)
mat<-t(mat)

## Compute Observed FD ("q" = 0)

## Create a list of repetition of communities

number<-seq(1,279,1)
list<-as.list(number)

## Create an empty dataframe to store the results

dataframe=data.frame()

for (number in list){
  
  result<-as.data.frame(FD_MLE(mat[,number], phylo.dist, mean(phylo.dist), 0))
  
  dataframe<-rbind(dataframe,result)
  
}

colnames(dataframe)<-'PD_q0'
dataframe$Site<-colnames(mat)
PD.0<-dataframe

## (A.1.2) Null FD 

## Now we need to randomize the community matrix from the global pool of species 

mat<-t(mat) ## Reorganize community data matrix as original - i.e. species as columns

library(picante)

dataframe.1=data.frame()
iteration=1:999

for(i in iteration) {
  
  reps = as.matrix(randomizeMatrix(mat, null.model = "independentswap"))
  reps<-t(reps)
  
  ## Create a list of repetition of communities
  
  number<-seq(1,279,1)
  list<-as.list(number)
  
  ## Create an empty dataframe to store the results
  
  dataframe=data.frame()
  
  for (number in list){
    
    result<-as.data.frame(FD_MLE(reps[,number], phylo.dist, mean(phylo.dist), 0))
    
    dataframe<-rbind(dataframe,result)
    
  }
  
  colnames(dataframe)<-'PD_q0'
  dataframe$Site<-colnames(reps)
  dataframe.1<-rbind(dataframe.1,dataframe)
  
}

## Calculate Mean and SD of the null community

summary<-dataframe.1%>%
  dplyr::group_by(Site)%>%
  dplyr::summarise(Mean_PD_q0=mean(PD_q0,na.rm = TRUE),
                   Sd_PD_q0=sd(PD_q0))%>%
  glimpse()

## Calculate SES FD (Rao Q)
## (SES = (obs - mean(null))/sd(null))

PD.0<-left_join(PD.0,summary,by=c("Site"))%>%glimpse()

PD.0<-PD.0%>%
  mutate(SES.PD_q0 = (PD_q0 - Mean_PD_q0)/Sd_PD_q0)%>%
  select(Site,PD_q0,SES.PD_q0)%>%
  glimpse()

## Calculate percetiles on the null distribution and classified communities: underdispersed (<5th), overdispersed (>95th) or random

quantile(dataframe.1$PD_q0, c(.05,0.25,0.75,0.95)) 

PD.0<-PD.0%>%
  mutate(p.PD.q0=ifelse(PD_q0<=1.876564,"Underdispersed (95%)",
                        ifelse(PD_q0<=3.213230,"Underdispersed (75%)",
                               ifelse(PD_q0>=5.516106,"Overdispersed (75%)",
                                      ifelse(PD_q0>=7.658069,"Overdispersed (95%)","Random")))))%>%
  glimpse()

## (B) "q" = 1 ----

## (A.1) Observed FD_q1

mat<-Abun

## Convert abundances to a list of N sites with abundances as vectors

mat<-as.matrix(mat)
mat<-t(mat)

## Compute Observed FD ("q" = 1)

## Create a list of repetition of communities

number<-seq(1,279,1)
list<-as.list(number)

## Create an empty dataframe to store the results

dataframe=data.frame()

for (number in list){
  
  result<-as.data.frame(FD_MLE(mat[,number], phylo.dist, mean(phylo.dist), 1))
  
  dataframe<-rbind(dataframe,result)
  
}

colnames(dataframe)<-'PD_q1'
dataframe$Site<-colnames(mat)
PD.1<-dataframe

## (A.1.2) Null FD 

## Now we need to randomize the community matrix from the global pool of species 

mat<-t(mat) ## Reorganize community data matrix as original - i.e. species as columns

library(picante)

dataframe.1=data.frame()
iteration=1:999

for(i in iteration) {
  
  reps = as.matrix(randomizeMatrix(mat, null.model = "independentswap"))
  reps<-t(reps)
  
  ## Create a list of repetition of communities
  
  number<-seq(1,279,1)
  list<-as.list(number)
  
  ## Create an empty dataframe to store the results
  
  dataframe=data.frame()
  
  for (number in list){
    
    result<-as.data.frame(FD_MLE(reps[,number], phylo.dist, mean(phylo.dist), 1))
    
    dataframe<-rbind(dataframe,result)
    
  }
  
  colnames(dataframe)<-'PD_q1'
  dataframe$Site<-colnames(reps)
  dataframe.1<-rbind(dataframe.1,dataframe)
  
}

## Calculate Mean and SD of the null community

summary<-dataframe.1%>%
  dplyr::group_by(Site)%>%
  dplyr::summarise(Mean_PD_q1=mean(PD_q1,na.rm = TRUE),
                   Sd_PD_q1=sd(PD_q1))%>%
  glimpse()

## Calculate SES FD (Rao Q)
## (SES = (obs - mean(null))/sd(null))

PD.1<-left_join(PD.1,summary,by=c("Site"))%>%glimpse()

PD.1<-PD.1%>%
  mutate(SES.PD_q1 = (PD_q1 - Mean_PD_q1)/Sd_PD_q1)%>%
  select(Site,PD_q1,SES.PD_q1)%>%
  glimpse()

## Calculate percetiles on the null distribution and classified communities: underdispersed (<5th), overdispersed (>95th) or random

quantile(dataframe.1$PD_q1, c(.05,0.25,0.75,0.95)) 

PD.1<-PD.1%>%
  mutate(p.PD.q1=ifelse(PD_q1<=1.088934,"Underdispersed (95%)",
                        ifelse(PD_q1<=1.681152,"Underdispersed (75%)",
                               ifelse(PD_q1>=2.980007,"Overdispersed (75%)",
                                      ifelse(PD_q1>=4.208608,"Overdispersed (95%)","Random")))))%>%
  glimpse()

## (C) "q" = 2 ----

## (A.1) Observed FD

mat<-Abun

## Convert abundances to a list of N sites with abundances as vectors

mat<-as.matrix(mat)
mat<-t(mat)

## Compute Observed FD ("q" = 2)

## Create a list of repetition of communities

number<-seq(1,279,1)
list<-as.list(number)

## Create an empty dataframe to store the results

dataframe=data.frame()

for (number in list){
  
  result<-as.data.frame(FD_MLE(mat[,number], phylo.dist, mean(phylo.dist), 2))
  
  dataframe<-rbind(dataframe,result)
  
}

colnames(dataframe)<-'PD_q2'
dataframe$Site<-colnames(mat)
PD.2<-dataframe

## (A.1.2) Null FD 

## Now we need to randomize the community matrix from the global pool of species 

mat<-t(mat) ## Reorganize community data matrix as original - i.e. species as columns

library(picante)

dataframe.1=data.frame()
iteration=1:999

for(i in iteration) {
  
  reps = as.matrix(randomizeMatrix(mat, null.model = "independentswap"))
  reps<-t(reps)
  
  ## Create a list of repetition of communities
  
  number<-seq(1,279,1)
  list<-as.list(number)
  
  ## Create an empty dataframe to store the results
  
  dataframe=data.frame()
  
  for (number in list){
    
    result<-as.data.frame(FD_MLE(reps[,number], phylo.dist, mean(phylo.dist), 2))
    
    dataframe<-rbind(dataframe,result)
    
  }
  
  colnames(dataframe)<-'PD_q2'
  dataframe$Site<-colnames(reps)
  dataframe.1<-rbind(dataframe.1,dataframe)
  
}

## Calculate Mean and SD of the null community

summary<-dataframe.1%>%
  dplyr::group_by(Site)%>%
  dplyr::summarise(Mean_PD_q2=mean(PD_q2,na.rm = TRUE),
                   Sd_PD_q2=sd(PD_q2))%>%
  glimpse()

## Calculate SES FD (Rao Q)
## (SES = (obs - mean(null))/sd(null))

PD.2<-left_join(PD.2,summary,by=c("Site"))%>%glimpse()

PD.2<-PD.2%>%
  mutate(SES.PD_q2 = (PD_q2 - Mean_PD_q2)/Sd_PD_q2)%>%
  select(Site,PD_q2,SES.PD_q2)%>%
  glimpse()

## Calculate percetiles on the null distribution and classified communities: underdispersed (<5th), overdispersed (>95th) or random

quantile(dataframe.1$PD_q2, c(.05,0.25,0.75,0.95)) 

PD.2<-PD.2%>%
  mutate(p.PD.q2=ifelse(PD_q2<=1.050977,"Underdispersed (95%)",
                        ifelse(PD_q2<=1.459365,"Underdispersed (75%)",
                               ifelse(PD_q2>=2.647502,"Overdispersed (75%)",
                                      ifelse(PD_q2>=3.762760,"Overdispersed","Random")))))%>%
  glimpse()

## Join datasets with original diversity metrics and export

diversity<-left_join(diversity,PD.0,by="Site")%>%glimpse()
diversity<-left_join(diversity,PD.1,by="Site")%>%glimpse()
diversity<-left_join(diversity,PD.2,by="Site")%>%glimpse()

## Export 

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity.25052021.csv")

#########################################################################################################################################
####################################### (5) Downloading LDG covariates #######################################################

citation('rgdal')

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

diversity<-read.csv("diversity_NEA_20201117.csv")%>%
  glimpse()

## Convert to a spatialpointsdataframe

coordinates(diversity)<-c("Longitude","Latitude") 
proj4string(diversity)<-CRS("+init=epsg:4326") ## Set the projection to WGS84
proj4string(diversity)
coordinates(diversity)

### Download broad-scale bioclimatic layers from BIORACLE AND MARSPEC

library(sdmpredictors)
citation('sdmpredictors')
citation('raster')

layers.bioracle <- list_layers( datasets="Bio-ORACLE") 
layers.bioracle 

layers.marspec <- list_layers( datasets="MARSPEC")
layers.marspec

# Download data of interest

bioracles.layers<-load_layers(layercodes = c("BO_sstmax","BO_sstmean","BO_sstmin","BO_sstrange",
                                             "BO2_salinitymax_ss","BO2_salinitymean_ss","BO2_salinitymin_ss","BO2_salinityrange_ss",
                                             "BO2_nitratemax_ss","BO2_nitratemean_ss","BO2_nitratemin_ss","BO2_nitraterange_ss",
                                             "BO2_phosphatemax_ss","BO2_phosphatemean_ss","BO2_phosphatemin_ss","BO2_phosphaterange_ss"),
                              equalarea=FALSE, rasterstack=TRUE) 


marspec.layers<-load_layers(layercodes = c("MS_biogeo06_bathy_slope_5m","MS_biogeo05_dist_shore_5m"), equalarea=FALSE, rasterstack=TRUE)

### Check covariates are in WGS84

### Bioracles layers

bioracles.layers
proj4string(bioracles.layers)
coordinates(bioracles.layers)

plot(bioracles.layers$BO_sstmin)
plot(diversity,add=T)

# Marspec.layers

proj4string(marspec.layers)
coordinates(marspec.layers)

plot(marspec.layers$MS_biogeo06_bathy_slope_5m)
plot(diversity,add=T)

## Extract environmental covariates

points.bioracle<-raster::extract(bioracles.layers,diversity,df=T,na.rm=TRUE,method='bilinear')

sum(is.na(points.bioracle))/prod(dim(points.bioracle))*100
apply(points.bioracle,2,function(col)sum(is.na(col))/length(col))*100

points.marspec<-raster::extract(marspec.layers,diversity,df=T,na.rm=TRUE,method='bilinear')

sum(is.na(points.marspec))/prod(dim(points.marspec))*100
apply(points.marspec,2,function(col)sum(is.na(col))/length(col))*100

## Reconvert diversity to a dataframe and join bioclimatic variables

diversity<-as.data.frame(diversity)%>%
  glimpse()

diversity<-bind_cols(diversity,points.bioracle,points.marspec)%>%
  glimpse()

## Extract coordinates from the dataset

coordinates<-diversity%>%
  dplyr::select(Latitude,Longitude)%>%
  glimpse()

## Export dataset and coordinates to extract covariates from the SEASYNC

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity_NEA_20201016.csv")
write.csv(coordinates,"coordinates.MARSPEC.csv")

## Bring in dataset with NPP and distance to market values incorporated

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

diversity<-read.csv("diversity_NEA_20201016.csv")%>%
  glimpse()

## Convert to a spatial object

coordinates(diversity)<-c("Longitude","Latitude") 
proj4string(diversity)<-CRS("+init=epsg:4326") ## Set the projection to WGS84
proj4string(diversity)
coordinates(diversity)

### Bring in LandsCan 2011 population density grid - in WGS84

setwd("C:/Users/22373243/Dropbox/Nestor_ascii_2/LandScan Global 2011/lspop2011") # For desktop directory
dir()
pop.den.data<-raster("dblbnd.adf")
projection(pop.den.data)
pop.den.data

### Extract population density values

points.50<-raster::extract(pop.den.data,diversity,buffer=50000,fun=sum,df=T,na.rm=T)
glimpse(points.50)
min(points.50$dblbnd)
max(points.50$dblbnd)
hist(points.50$dblbnd)
sum(is.na(points.50))

points.100<-raster::extract(pop.den.data,diversity,buffer=100000,fun=sum,df=T,na.rm=T)
glimpse(points.100)
min(points.100$dblbnd)
max(points.100$dblbnd)
hist(points.100$dblbnd)
sum(is.na(points.100$dblbnd))

points.200<-raster::extract(pop.den.data,diversity,buffer=200000,fun=sum,df=T,na.rm=T)
glimpse(points.200)
min(points.200$dblbnd)
max(points.200$dblbnd)
hist(points.200$dblbnd)
sum(is.na(points.200$dblbnd))

## Recovert diversity into a dataframe

diversity<-as.data.frame(diversity)%>%
  glimpse()

## Join Human Population values with diversity dataframe

diversity<-bind_cols(diversity,points.50,points.100,points.200)%>%
  glimpse()

## Rename Human population buffers and delete ID columns

diversity<-diversity%>%
  dplyr::rename(pop.den.50=dblbnd,
                pop.den.100=dblbnd1,
                pop.den.200=dblbnd2)%>%
  dplyr::select(-ID2,-ID3,-ID4)%>%
  glimpse()

## Bring in dat and extract average depth for a site

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Raw')
dir()

dat<-read.csv("NEA_analyses.csv")%>%
  dplyr::select(Site,Depth)%>%
  # mutate(Abun=log1p(response))%>% ## Transform species abundances to balance the contribution of dominant and rare species
  glimpse()

diversity<-left_join(diversity,dat,by="Site")%>%
  glimpse()
sum(is.na(diversity$Depth))

## Remove duplicates

diversity<-diversity%>%
  distinct(Site,Latitude,Longitude,.keep_all = TRUE)%>%
  glimpse()

## Convert to a spatial object

coordinates(diversity)<-c("Longitude","Latitude") 
proj4string(diversity)<-CRS("+init=epsg:4326") ## Set the projection to WGS84
proj4string(diversity)
coordinates(diversity)

### Extract MPA data from Global Protected Areas database (IUCN)

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Shapefiles/MPAs')
dir()

mpa<-readOGR('.','WDPA_May2020_marine-shapefile-polygons')
proj4string(mpa)

glimpse(mpa@data)

## Join MPA information from the World Protected Area Database to Diversity dataset

library(spatialEco)

mpa.points<-point.in.poly(diversity,mpa)
glimpse(mpa.points@data)

### Reconvert diversity into a dataframe and export

diversity<-as.data.frame(mpa.points)%>%
  glimpse()
glimpse(diversity)

## Clean up the diversity dataset

diversity<-diversity%>%
  dplyr::rename(Longitude=coords.x1,
                Latitude=coords.x2)%>%
  glimpse()

unique(diversity$MARINE)

diversity<-diversity%>%
  dplyr::select(-ID,-ID1,-WDPAID,-WDPA_PID,-PA_DEF,-ORIG_NAME,-DESIG,-INT_CRIT,-GIS_M_AREA,-REP_AREA,-GIS_AREA,
                -MANG_PLAN,-VERIF,-METADATAID,-SUB_LOC,-PARENT_ISO,-ISO3)%>%
  glimpse()

## Create Status category based on IUCN categories

glimpse(diversity)
unique(diversity$IUCN_CAT)

diversity<-diversity%>%
  mutate(Status=ifelse(IUCN_CAT%in%c('<NA>','Not Reported','Not Assigned'),"Fished",
                       ifelse(IUCN_CAT%in%c('Ia','Ib','II'),"No-take","Restricted Fishing")))%>%
  glimpse()

## Exclude duplicated sites

diversity<-diversity%>%
  distinct(Site,Latitude,Longitude,.keep_all = TRUE)%>%
  glimpse()

## Export dataframe and check that Regulations apply when the sampling occurred

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity_NEA_20201017.csv")

####### Explore distance to the nearest continental mass metric ----

ggplot(diversity,aes(x=Dst2continent,fill=Ecoregion))+
  geom_density(colour="black")+
  facet_wrap(~Ecoregion,scale="free_x")+
  theme_classic()+
  Theme1

###### Download bathymrety layer from MARSPEC

library(sdmpredictors)

layers.marspec <- list_layers( datasets="MARSPEC")
layers.marspec

marspec.layers<-load_layers(layercodes = c("MS_bathy_5m"), equalarea=FALSE, rasterstack=TRUE)
plot(marspec.layers$MS_bathy_5m)

setwd("C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Shapefiles/MARSPEC/Contemporary")
dir()

writeRaster(marspec.layers,"Bathymetry.tif")

## Try BIORACLE layer

layers.bioracle <- list_layers( datasets="Bio-ORACLE") 
layers.bioracle 

bioracles.layers<-load_layers(layercodes = c("BO_bathymax"),
                              equalarea=FALSE, rasterstack=TRUE) 

plot(bioracles.layers$BO_bathymax)

## Export BIORACLE Bathymetry

setwd("C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Shapefiles/MARSPEC/Contemporary")
dir()

writeRaster(bioracles.layers,"Bathymetry_BIORACLE_max.tif")

## Filter depths < 200 m

bioracles.layers[bioracles.layers<(-200)]<-NA
bioracles.layers[bioracles.layers>0]<-NA
bioracles.layers<-abs(bioracles.layers)
plot(bioracles.layers)

## Export new layers

writeRaster(bioracles.layers,"Bathymetry_BIORACLE_200m_max_abs.tif")

###### Calculate Continental Shelf Area ----

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

diversity<-read.csv("diversity_NEA_20201117.csv")%>%
  glimpse()

## Convert to a spatial object

coordinates(diversity)<-c("Longitude","Latitude") 
proj4string(diversity)<-CRS("+init=epsg:4326") ## Set the projection to WGS84
proj4string(diversity)
coordinates(diversity)

## Read new MARSPEC bathymetry

setwd("C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Shapefiles/MARSPEC/Contemporary")
dir()

depth<-raster("bathy_30s.tif")

## Crop to the Atlantic basin extent

e<-extent(-32,20,-24,90,-35)
depth<-crop(depth,e)
plot(depth)

## Mask to depth between 0 - 200 m

depth[depth>0]<-NA
depth<-abs(depth)
depth[depth>200]<-NA
plot(depth)

## Bring in Marine Ecoregions of the World

setwd("C:/Users/22373243/Dropbox/Nestor_ascii_2/MEOW")
dir()

marine.ecoregions<-readOGR('.','meow_ecos')
proj4string(marine.ecoregions)
marine.ecoregions<-crop(marine.ecoregions,e)
plot(marine.ecoregions)

## Filter a Ecoregion

unique(diversity$Ecoregion)

test<-subset(marine.ecoregions, ECOREGION=="North Sea")
plot(test)

## Mask raster to shapefile polygon

test.depth<-mask(depth,test,inverse=F)
test.depth
plot(test.depth,add=TRUE)

## Obtain area of the cells within Ecoregion

a<-area(test.depth)
a<-mask(a,test.depth)
plot(a,add=TRUE)

sum(values(a), na.rm = TRUE)

####### Calculate connectivity potential ----
## (1) Number of cells in a radius of 600-km with depths range between 0 - 30 m
## (2) Number of cells in a radius of 600-lm with depths range between 0 - 200m

plot(depth)

## Create additional raster filtering depths > 30 m

depth.30m<-depth
depth.30m[depth.30m>30]<-NA
plot(depth.30m)

## Convert to a single numeric unit (1) to count the number of cells

test<-depth
values(test)<-1
test<-mask(test,depth)
plot(test)

## Extract the sum of area within a 600-km buffer for 0 - 200 m range

points<-raster::extract(test,diversity,buffer=600000,fun=sum,df=T,na.rm=T)
colnames(points)<-c('ID','Connectivity_200m')
glimpse(points)

## Join with dataset

diversity$Connec_200m<-points$Connectivity_200m
glimpse(diversity@data)

### Connectivity to shallow (0 - 30 m)

points<-raster::extract(test,diversity,buffer=600000,fun=sum,df=T,na.rm=T)
colnames(points)<-c('ID','Connectivity_30m')
glimpse(points)

## Join with dataset

diversity$Connec_30m<-points$Connectivity_30m
glimpse(diversity@data)

## Reconvert to a dataframe

diversity<-as.data.frame(diversity)%>%
  glimpse()

## Export diversity dataframe

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity_NEA_20201117.csv")

## Calculate CWM body size ----

CWM_df<-rownames_to_column(CWM_df, var = "Site")

CWM_df<-CWM_df%>%
  dplyr::select(Site,MaxLength)%>%
  glimpse()

### Bring in diversity dataset

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()  

diversity<-read.csv("diversity_NEA_20201117.csv")%>%
  dplyr::select(-MaxLength)%>%
  glimpse()

## Join CWM body size

diversity<-left_join(diversity,CWM_df,by="Site")%>%
  glimpse()

sum(is.na(CWM_df$MaxLength))

## Export dataset

write.csv(diversity,"diversity_NEA_20201117.csv")

###############################################################################################################################
######################################## (6) GAM - LDG ###################################################

## Bring in diversity dataset

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

diversity<-read.csv('diversity.25052021.csv')%>%
  glimpse()

## (A) Correlation between diversity indices ----

library(PerformanceAnalytics)

names(diversity)
my_data <- diversity[, c("TD_q0","TD_q1","TD_q2","SES.FD_q0","SES.FD_q1","SES.FD_q2",
                         "SES.PD_q0","SES.PD_q1","SES.PD_q2")]
chart.Correlation(my_data, histogram=TRUE, pch=19)

## (B) Raw data values highlighting null values, and significant under- and over-dispersion ----

## Reorder levels of the factor

library(forcats)
library(plyr)

levels(diversity$Ecoregion)

diversity<-diversity%>%
  mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Webbnesia",
                               "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

## Taxonomic diversity

TD.0<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=TD_q0,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  ggtitle('(a)')+
  ylab('Taxonomic Diversity')+
  xlab('Latitude (°)')+
  ylim(1,33)+
  theme_classic()+
  Theme1
TD.0

TD.1<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=TD_q1,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  ggtitle('(b)')+
  ylab('')+
  xlab('Latitude (°)')+
  ylim(1,33)+
  theme_classic()+
  Theme1
TD.1

TD.2<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=TD_q2,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  ggtitle('(c)')+
  ylab('')+
  xlab('Latitude (°)')+
  ylim(1,33)+
  theme_classic()+
  Theme1
TD.2

## Arrange and fix y-axis

ggarrange(TD.0,TD.1,TD.2,nrow=1,ncol=3,align = 'hv')

## Functional Diversity

FD.0<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=SES.FD_q0,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ggtitle('(d)')+
  ylab('Functional Diversity')+
  xlab('Latitude (°)')+
  ylim(-2.2,2.2)+
  theme_classic()+
  Theme1
FD.0

FD.1<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=SES.FD_q1,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ggtitle('(e)')+
  ylab('')+
  xlab('Latitude (°)')+
  ylim(-2.2,2.2)+
  theme_classic()+
  Theme1
FD.1

FD.2<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=SES.FD_q2,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ggtitle('(f)')+
  ylab('')+
  xlab('Latitude (°)')+
  ylim(-2.2,2.2)+
  theme_classic()+
  Theme1
FD.2

## Arrange and fix y-axis

ggarrange(FD.0,FD.1,FD.2,nrow=1,ncol=3,align = 'hv')

## Phylogenetic diversity

PD.0<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=SES.PD_q0,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ggtitle('(g)')+
  ylab('Phylogenetic Diversity')+
  xlab('Latitude (°)')+
  ylim(-3,2)+
  theme_classic()+
  Theme1
PD.0

PD.1<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=SES.PD_q1,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = F)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ggtitle('(h)')+
  ylab('')+
  xlab('Latitude (°)')+
  ylim(-3,2)+
  theme_classic()+
  Theme1
PD.1

PD.2<-ggplot()+
  geom_point(data=diversity,aes(x=Latitude,y=SES.PD_q2,shape=Ecoregion,fill=Ecoregion),size=2,show.legend = T)+
  scale_shape_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                                "South European Atlantic Shelf","Celtic Seas",
                                "North Sea"),values=c(21, 8, 23, 24, 25, 22))+
  scale_fill_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Macaronesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ggtitle('(i)')+
  ylab('')+
  xlab('Latitude (°)')+
  ylim(-3,2)+
  theme_classic()+
  Theme1
PD.2

## Arrange and fix y-axis

ggarrange(PD.0,PD.1,PD.2,nrow=1,ncol = 3,align = 'hv',legend = "none")

## Arrange plots in a grob

ggarrange(TD.0,TD.1,TD.2,FD.0,FD.1,FD.2,PD.0,PD.1,PD.2,
          ncol=3,nrow=3,align = 'hv',legend = "bottom",common.legend = TRUE)

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/Supplementary_materials')

name<-'Supp_Fig1_Diversity_Raw'

ggsave(paste(name,".png",sep="."),width = 21, height = 20,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 21, height = 20,units = "cm",dpi=600,useDingbats=FALSE)

## Clean the working directory

rm(TD.0,TD.1,TD.2,FD.0,FD.1,FD.2,PD.0,PD.1,PD.2,my_data)

## (C) Run regression of metrics against Total number of individuals at a site ----
## To correct for variable sampling effort - Edgar et al. 2017

## (A) D0 

hist(log1p(diversity$TD_q0))
hist(log1p(diversity$Total_Abun))

lm.richness<-lm(log1p(TD_q0) ~ log1p(Total_Abun),data = diversity)
summary(lm.richness)
plot(lm.richness)

D0<-ggplot(diversity,aes(x=log1p(Total_Abun),y=log1p(TD_q0)))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(a)')+
  theme_classic()+
  Theme1
D0

## (B) D1

hist(log1p(diversity$TD_q1))
hist(log1p(diversity$Total_Abun))

lm.D1<-lm(log1p(TD_q1) ~ log1p(Total_Abun),data = diversity)
summary(lm.D1)
plot(lm.D1)

D1<-ggplot(diversity,aes(x=log1p(Total_Abun),y=log1p(TD_q1)))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(b)')+
  theme_classic()+
  Theme1
D1

## (C) D2

hist(log1p(diversity$TD_q2))
hist(log1p(diversity$Total_Abun))

lm.D2<-lm(log1p(TD_q2) ~ log1p(Total_Abun),data = diversity)
summary(lm.D2)
plot(lm.D2)

D2<-ggplot(diversity,aes(x=log1p(Total_Abun),y=log1p(TD_q2)))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(c)')+
  theme_classic()+
  Theme1
D2

## (D) FD0

hist(diversity$SES.FD_q0)
hist(log1p(diversity$Total_Abun))

lm.FD_q0<-lm(SES.FD_q0 ~ log1p(Total_Abun),data = diversity)
summary(lm.FD_q0)
plot(lm.FD_q0)

FD0<-ggplot(diversity,aes(x=log1p(Total_Abun),y=SES.FD_q0))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(d)')+
  theme_classic()+
  Theme1
FD0

## (E) FD1

hist(diversity$SES.FD_q1)
hist(log1p(diversity$Total_Abun))

lm.FD1<-lm(SES.FD_q1 ~ log1p(Total_Abun),data = diversity)
summary(lm.FD1)
plot(lm.FD1)

FD1<-ggplot(diversity,aes(x=log1p(Total_Abun),y=SES.FD_q1))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(e)')+
  theme_classic()+
  Theme1

FD1

## (F) FD2

hist(diversity$SES.FD_q2)
hist(log1p(diversity$Total_Abun))

lm.FD_q2<-lm(SES.FD_q2 ~ log1p(Total_Abun),data = diversity)
summary(lm.FD_q2)
plot(lm.FD_q2)

FD2<-ggplot(diversity,aes(x=log1p(Total_Abun),y=SES.FD_q2))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(f)')+
  theme_classic()+
  Theme1

FD2

## (g) PD0

hist(diversity$SES.PD_q0)
hist(log1p(diversity$Total_Abun))

lm.PD.q0<-lm(SES.PD_q0 ~ log1p(Total_Abun),data = diversity)
summary(lm.PD.q0)
plot(lm.PD.q0)

PD0<-ggplot(diversity,aes(x=log1p(Total_Abun),y=SES.PD_q0))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(g)')+
  theme_classic()+
  Theme1

PD0

## (h) PD1

hist(diversity$SES.PD_q1)
hist(log1p(diversity$Total_Abun))

lm.PD.q1<-lm(SES.PD_q1 ~ log1p(Total_Abun),data = diversity)
summary(lm.PD.q1)
plot(lm.PD.q1)

PD1<-ggplot(diversity,aes(x=log1p(Total_Abun),y=SES.PD_q1))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(h)')+
  theme_classic()+
  Theme1

PD1

## (i) PD2

hist(diversity$SES.PD_q2)
hist(log1p(diversity$Total_Abun))

lm.PD.q2<-lm(SES.PD_q2 ~ log1p(Total_Abun),data = diversity)
summary(lm.PD.q2)
plot(lm.PD.q2)

PD2<-ggplot(diversity,aes(x=log1p(Total_Abun),y=SES.PD_q2))+
  geom_point()+
  stat_smooth(method = "lm")+
  ggtitle('(i)')+
  theme_classic()+
  Theme1

PD2

## Arrange plots in a grob

ggarrange(D0,D1,D2,FD0,FD1,FD2,PD0,PD1,PD2,
          ncol=3,nrow=3,align = 'hv',legend = "bottom",common.legend = TRUE)

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Supp_Fig2_Abundance_Effect_20210525'

ggsave(paste(name,".png",sep="."),width = 21, height = 20,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 21, height = 20,units = "cm",dpi=600,useDingbats=FALSE)

## Extract residuals from models - i.e. new metric corrected for total abundance at a site

res1<-resid(lm.richness)
res2<-resid(lm.D1)
res3<-resid(lm.D2)
res4<-resid(lm.FD_q0)
res5<-resid(lm.FD1)
res6<-resid(lm.FD_q2)
res7<-resid(lm.PD.q0)
res8<-resid(lm.PD.q1)
res9<-resid(lm.PD.q2)

## Join residuals in the diversity data - i.e. new metric corrected for total abundance at a site

diversity$richness.res<-res1
diversity$diversity.q1.res<-res2
diversity$diversity.q2.res<-res3

## Need to filter NAs from SES FD (3 sites) and SES PD (8 sites) to join values

## FD

FD.test<-diversity%>%
  filter(!is.na(SES.FD_q0))%>%
  glimpse()
names<-as.vector(unique(FD.test$Site))

res4<-as.data.frame(res4)
colnames(res4)<-'FD_q0.res'
res4$Site<-names
res4$FD_q1.res<-res5
res4$FD_q2.res<-res6

diversity<-left_join(diversity,res4,by="Site")%>%glimpse()

glimpse(diversity)

## PD

PD.test<-diversity%>%
  filter(!is.na(SES.PD_q0))%>%
  glimpse()
names<-as.vector(unique(PD.test$Site))

res7<-as.data.frame(res7)
colnames(res7)<-'PD_q0.res'
res7$Site<-names
res7$PD_q1.res<-res8
res7$PD_q2.res<-res9

diversity<-left_join(diversity,res7,by="Site")%>%glimpse()

glimpse(diversity)

## Export diversity dataset with residuals incorporated

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(diversity,"diversity.06052021.csv")

## Clean working directory

rm(FD.test,lm.D1,lm.D2,lm.PD.q0,lm.FD_q0,lm.FD_q2,lm.FD_q2,FD0,FD1,FD2,PD0,PD1,PD2,
   lm.PD.q1,lm.PD.q2,PD.test,res4,res7,lm.richness,lm.FD1,D0,D1,D2)

########## (D) Run Generalized Additive Models in Model residuals ----

## Load libraries

library(mgcv)
library(mgcViz)

## Bring in diversity indices

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

diversity<-read.csv('diversity.25052021.csv')%>%
  glimpse()

## Transform response variables

diversity$TD_q0<-sqrt(diversity$TD_q0)
diversity$TD_q1<-log1p(diversity$TD_q1)
diversity$TD_q2<-log1p(diversity$TD_q2)

################# Taxonomic diversity ----

## (A) D0

hist(diversity$richness.res)

D0.gam=gam(richness.res ~ s(Latitude,bs="cr",k=5),
           family = gaussian(),data=diversity)
plot(D0.gam,all.terms=T,pages=1,residuals = T)
summary(D0.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(D0.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(D0.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.D0 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.D0,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.D0<-read.csv("predicts.csv")%>%
  glimpse()

## (B) D1

hist(diversity$diversity.q1.res)

D1.gam=gam(diversity.q1.res ~ s(Latitude,k=5,bs="cr"),
           family = gaussian(),data=diversity)
plot(D1.gam,all.terms=T,pages=1,residuals = T)
summary(D1.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(D1.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(D1.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.D1 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.D1,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.D1<-read.csv("predicts.csv")%>%
  glimpse()

## (C) D2

hist(diversity$diversity.q2.res)

D2.gam=gam(diversity.q2.res ~ s(Latitude,k=5,bs="cr"),
           family = gaussian(),data=diversity)
plot(D2.gam,all.terms=T,pages=1,residuals = T)
summary(D2.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(D2.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(D2.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.D2 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.D2,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.D2<-read.csv("predicts.csv")%>%
  glimpse()

## Plot

TD<-ggplot()+
  geom_line(data=La.predicts.D0,aes(x=Latitude,y=response),colour="black",size=1)+
  geom_line(data=La.predicts.D0,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="black",size=1,alpha=1)+
  geom_line(data=La.predicts.D0,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="black",size=1,alpha=1)+
  geom_line(data=La.predicts.D1,aes(x=Latitude,y=response),colour="darkgrey",size=1)+
  geom_line(data=La.predicts.D1,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="darkgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.D1,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="darkgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.D2,aes(x=Latitude,y=response),colour="lightgrey",size=1)+
  geom_line(data=La.predicts.D2,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="lightgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.D2,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="lightgrey",size=1,alpha=1)+
  ggtitle('(a)')+
  ylab('Taxonomic diversity')+
  xlab('Latitude (°)')+
  theme_classic()+
  Theme1
TD

################# Functional Diversity ----

## (A) FD0

hist(diversity$FD_q0.res)

FD0.gam=gam(FD_q0.res ~ s(Latitude,k=5,bs="cr"),
           family = gaussian(),data=diversity)
plot(FD0.gam,all.terms=T,pages=1,residuals = T)
summary(FD0.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(FD0.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(FD0.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.FD0 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.FD0,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.FD0<-read.csv("predicts.csv")%>%
  glimpse()

## (B) FD1

hist(diversity$FD_q1.res)

FD1.gam=gam(FD_q1.res ~ s(Latitude,k=5,bs="cr"),
           family = gaussian(),data=diversity)
plot(FD1.gam,all.terms=T,pages=1,residuals = T)
summary(FD1.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(FD1.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(FD1.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.FD1 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.FD1,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.FD1<-read.csv("predicts.csv")%>%
  glimpse()

## (C) FD2

hist(diversity$FD_q2.res)

FD2.gam=gam(FD_q2.res ~ s(Latitude,k=5,bs="cr"),
           family = gaussian(),data=diversity)
plot(FD2.gam,all.terms=T,pages=1,residuals = T)
summary(FD2.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(FD2.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(FD2.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.FD2 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.FD2,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.FD2<-read.csv("predicts.csv")%>%
  glimpse()

## Plot

FD<-ggplot()+
  geom_line(data=La.predicts.FD0,aes(x=Latitude,y=response),colour="black",size=1)+
  geom_line(data=La.predicts.FD0,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="black",size=1,alpha=1)+
  geom_line(data=La.predicts.FD0,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="black",size=1,alpha=1)+
  geom_line(data=La.predicts.FD1,aes(x=Latitude,y=response),colour="darkgrey",size=1)+
  geom_line(data=La.predicts.FD1,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="darkgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.FD1,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="darkgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.FD2,aes(x=Latitude,y=response),colour="lightgrey",size=1)+
  geom_line(data=La.predicts.FD2,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="lightgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.FD2,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="lightgrey",size=1,alpha=1)+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ylim(-1,1)+
  ggtitle('(b)')+
  ylab('Functional diversity')+
  xlab('Latitude (°)')+
  theme_classic()+
  Theme1
FD

################# Phylogenetic Diversity ----

## (A) PD0

hist(diversity$PD_q0.res)

PD0.gam=gam(PD_q0.res ~ s(Latitude,k=5,bs="cr"),
            family = gaussian(),data=diversity)
plot(PD0.gam,all.terms=T,pages=1,residuals = T)
summary(PD0.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(PD0.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(PD0.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.PD0 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.PD0,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.PD0<-read.csv("predicts.csv")%>%
  glimpse()

## (B) PD1

hist(diversity$PD_q1.res)

PD1.gam=gam(PD_q1.res ~ s(Latitude,k=5,bs="cr"),
            family = gaussian(),data=diversity)
plot(PD1.gam,all.terms=T,pages=1,residuals = T)
summary(PD1.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(PD1.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(PD1.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.PD1 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.PD1,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.PD1<-read.csv("predicts.csv")%>%
  glimpse()

## (C) FD2

hist(diversity$PD_q2.res)

PD2.gam=gam(PD_q2.res ~ s(Latitude,k=5,bs="cr"),
            family = gaussian(),data=diversity)
plot(PD2.gam,all.terms=T,pages=1,residuals = T)
summary(PD2.gam)

## Check of residuals

plot.new()
par(mfrow=c(2,2))
gam.check(PD2.gam)

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(diversity$Latitude),max(diversity$Latitude), length = 100))%>%
  glimpse()

xp <- predict(PD2.gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.PD2 = pdat%>%data.frame(xp)%>%
  group_by(Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.PD2,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.PD2<-read.csv("predicts.csv")%>%
  glimpse()

## Plot

PD<-ggplot()+
  geom_line(data=La.predicts.PD0,aes(x=Latitude,y=response),colour="black",size=1,show.legend = T)+
  geom_line(data=La.predicts.PD0,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="black",size=1,alpha=1)+
  geom_line(data=La.predicts.PD0,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="black",size=1,alpha=1)+
  geom_line(data=La.predicts.PD1,aes(x=Latitude,y=response),colour="darkgrey",size=1,show.legend = T)+
  geom_line(data=La.predicts.PD1,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="darkgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.PD1,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="darkgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.PD2,aes(x=Latitude,y=response),colour="lightgrey",size=1,show.legend = T)+
  geom_line(data=La.predicts.PD2,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="lightgrey",size=1,alpha=1)+
  geom_line(data=La.predicts.PD2,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="lightgrey",size=1,alpha=1)+
  geom_hline(yintercept = 0,linetype="dashed",size=1)+
  ylim(-1,1)+
  ggtitle('(c)')+
  ylab('Phylogenetic diversity')+
  xlab('Latitude (°)')+
  theme_classic()+
  Theme1
PD

## Arrange plots in a grob

ggarrange(TD,FD,PD,ncol=3,nrow=1,align = 'hv',legend = "bottom",common.legend = TRUE)

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Fig2_LDG_Corrected_20210525'

ggsave(paste(name,".png",sep="."),width = 21, height = 9,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 21, height = 9,units = "cm",dpi=600,useDingbats=FALSE)

### Investigate spatial autocorrelation in the residuals of the models ----

## Extract model residuals

res1<-residuals.gam(D0.gam)
res2<-residuals.gam(D1.gam)
res3<-residuals.gam(D2.gam)
res4<-residuals.gam(FD0.gam)
res5<-residuals.gam(FD1.gam)
res6<-residuals.gam(FD2.gam)
res7<-residuals.gam(PD0.gam)
res8<-residuals.gam(PD1.gam)
res9<-residuals.gam(PD2.gam)

## Join residuals to dataset

diversity$res.D0<-res1
diversity$res.D1<-res2
diversity$res.D2<-res3

## Need to filter NAs in SES FD (3 sites) and SES PD (8 sites)

## FD

FD.test<-diversity%>%
  filter(!is.na(SES.FD_q0))%>%
  glimpse()
names<-as.vector(unique(FD.test$Site))

FD.res<-as.data.frame(res4)
colnames(FD.res)<-'res.FD0'
FD.res$Site<-names
FD.res$res.FD1<-res5
FD.res$res.FD2<-res6

diversity<-left_join(diversity,FD.res,by="Site")%>%glimpse()

## PD

PD.test<-diversity%>%
  filter(!is.na(SES.PD_q0))%>%
  glimpse()
names<-as.vector(unique(PD.test$Site))

PD.res<-as.data.frame(res7)
colnames(PD.res)<-'res.PD0'
PD.res$Site<-names
PD.res$res.PD1<-res8
PD.res$res.PD2<-res9

diversity<-left_join(diversity,PD.res,by="Site")%>%glimpse()

## Plot residuals to check

plot.new()
par(mfrow=c(3,3))

hist(diversity$res.D0)
hist(diversity$res.D1)
hist(diversity$res.D2)
hist(diversity$res.FD0)
hist(diversity$res.FD1)
hist(diversity$res.FD2)
hist(diversity$res.PD0)
hist(diversity$res.PD1)
hist(diversity$res.PD2)

### Check residual auto-correlation via spded package

## Convert into an spatial object

coordinates(diversity)<-~Longitude+Latitude
class(diversity)

## Set the CRS

proj4string(diversity)<-CRS("+init=epsg:4326")
diversity@proj4string

## FD

FD.test<-as.data.frame(diversity)%>%
  filter(!is.na(res.FD0))%>%
  glimpse()

## Convert into a spatial object

coordinates(FD.test)<-~Longitude+Latitude
class(FD.test)

## Set the CRS

proj4string(FD.test)<-CRS("+init=epsg:4326")
FD.test@proj4string

## PD

PD.test<-as.data.frame(diversity)%>%
  filter(!is.na(res.PD0))%>%
  glimpse()

## Convert into a spatial object

coordinates(PD.test)<-~Longitude+Latitude
class(PD.test)

## Set the CRS

proj4string(PD.test)<-CRS("+init=epsg:4326")
PD.test@proj4string

## Compute semivariogram

library(gstat)
citation('gstat')

## TD

D0.variogram<-variogram(diversity$res.D0~1,data=diversity,cutoff=100,width=1)
plot(D0.variogram,main="(a)",ylab="Semivariance",xlab="Distance (km)")

D1.variogram<-variogram(diversity$res.D1~1,data=diversity,cutoff=100,width=1)
plot(D1.variogram,main="(b)",ylab="Semivariance",xlab="Distance (km)")

D2.variogram<-variogram(diversity$res.D2~1,data=diversity,cutoff=100,width=1)
plot(D2.variogram,main="(c)",ylab="Semivariance",xlab="Distance (km)")

## FD

FD0.variogram<-variogram(FD.test$res.FD0~1,data=FD.test,cutoff=100,width=1,na.omit=T)
plot(FD0.variogram,main="(d)",ylab="Semivariance",xlab="Distance (km)")

FD1.variogram<-variogram(FD.test$res.FD1~1,data=FD.test,cutoff=100,width=1)
plot(FD1.variogram,main="(e)",ylab="Semivariance",xlab="Distance (km)")

FD2.variogram<-variogram(FD.test$res.FD2~1,data=FD.test,cutoff=100,width=1)
plot(FD2.variogram,main="(f)",ylab="Semivariance",xlab="Distance (km)")

## TD 

PD0.variogram<-variogram(PD.test$res.PD0~1,data=PD.test,cutoff=100,width=1)
plot(PD0.variogram,main="(g)",ylab="Semivariance",xlab="Distance (km)")

PD1.variogram<-variogram(PD.test$res.PD1~1,data=PD.test,cutoff=100,width=1)
plot(PD1.variogram,main="(h)",ylab="Semivariance",xlab="Distance (km)")

PD2.variogram<-variogram(PD.test$res.PD2~1,data=PD.test,cutoff=100,width=1)
plot(PD2.variogram,main="(i)",ylab="Semivariance",xlab="Distance (km)")

## Calculate Global Moran's I

## TD

library(geosphere)

dists <- distm(diversity, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) ## 5398.58

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)
citation('ape')

## Legal (response)

Moran.I(diversity$res.D0,dists.inv)
Moran.I(diversity$res.D1,dists.inv)
Moran.I(diversity$res.D2,dists.inv)

## FD

library(geosphere)

dists <- distm(FD.test, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) ## 5398.58

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

Moran.I(FD.test$res.FD0,dists.inv)
Moran.I(FD.test$res.FD1,dists.inv)
Moran.I(FD.test$res.FD2,dists.inv)

## PD

library(geosphere)

dists <- distm(PD.test, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) ## 5398.58

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct


Moran.I(PD.test$res.PD0,dists.inv)
Moran.I(PD.test$res.PD1,dists.inv)
Moran.I(PD.test$res.PD2,dists.inv)

glimpse(diversity)

####################################################################################################
############################ (7) Relative importance of assembly rules across LDG ##################

## Bring in diversity dataset

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

diversity<-read.csv('diversity.25052021.csv')%>%
  glimpse()

## Reorder levels of the factor for plotting

library(forcats)

unique(diversity$Ecoregion)

diversity<-diversity%>%
  mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Webbnesia",
                               "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

## (A) FD_q0 ----

## Calculate the relative frequency of each assembly rule - Neutral, Underdispersed, Overdispersed

FD.q0.rules=data.frame()

ecoregion<-as.vector(unique(diversity$Ecoregion)) ## For n in Ecoregions

for (i in ecoregion) {
  
  ## Create frequency of occurrence for each latitudinal bin and frequency class
  
  test<-diversity%>%
    filter(Ecoregion%in%i)%>%
    glimpse()
  n<-as.numeric(nrow(test))
  
  test.1<-test%>%
    dplyr::group_by(Ecoregion,p.FD.q0)%>%
    dplyr::summarise(number=n())%>%
    mutate(percentage=(number/n)*100)%>%
    ungroup()%>%
    glimpse()
  
  FD.q0.rules<-rbind(FD.q0.rules,test.1)
  
}

## (B) FD_q1 ----

## Calculate the relative frequency of each assembly rule - Neutral, Underdispersed, Overdispersed

FD.q1.rules=data.frame()

ecoregion<-as.vector(unique(diversity$Ecoregion)) ## For n in Ecoregions

for (i in ecoregion) {
  
  ## Create frequency of occurrence for each latitudinal bin and frequency class
  
  test<-diversity%>%
    filter(Ecoregion%in%i)%>%
    glimpse()
  n<-as.numeric(nrow(test))
  
  test.1<-test%>%
    dplyr::group_by(Ecoregion,p.FD.q1)%>%
    dplyr::summarise(number=n())%>%
    mutate(percentage=(number/n)*100)%>%
    ungroup()%>%
    glimpse()
  
  FD.q1.rules<-rbind(FD.q1.rules,test.1)
  
}

## (C) FD_q2 ----

## Calculate the relative frequency of each assembly rule - Neutral, Underdispersed, Overdispersed

FD.q2.rules=data.frame()

ecoregion<-as.vector(unique(diversity$Ecoregion)) ## For n in Ecoregions

for (i in ecoregion) {
  
  ## Create frequency of occurrence for each latitudinal bin and frequency class
  
  test<-diversity%>%
    filter(Ecoregion%in%i)%>%
    glimpse()
  n<-as.numeric(nrow(test))
  
  test.1<-test%>%
    dplyr::group_by(Ecoregion,p.FD.q2)%>%
    dplyr::summarise(number=n())%>%
    mutate(percentage=(number/n)*100)%>%
    ungroup()%>%
    glimpse()
  
  FD.q2.rules<-rbind(FD.q2.rules,test.1)
  
}

## (D) PD_q0 ----

## Calculate the relative frequency of each assembly rule - Neutral, Underdispersed, Overdispersed

PD.q0.rules=data.frame()

ecoregion<-as.vector(unique(diversity$Ecoregion)) ## For n in Ecoregions

for (i in ecoregion) {
  
  ## Create frequency of occurrence for each latitudinal bin and frequency class
  
  test<-diversity%>%
    filter(Ecoregion%in%i)%>%
    glimpse()
  n<-as.numeric(nrow(test))
  
  test.1<-test%>%
    dplyr::group_by(Ecoregion,p.PD.q0)%>%
    dplyr::summarise(number=n())%>%
    mutate(percentage=(number/n)*100)%>%
    ungroup()%>%
    glimpse()
  
  PD.q0.rules<-rbind(PD.q0.rules,test.1)
  
}

## (E) PD_q1 ----

## Calculate the relative frequency of each assembly rule - Neutral, Underdispersed, Overdispersed

PD.q1.rules=data.frame()

ecoregion<-as.vector(unique(diversity$Ecoregion)) ## For n in Ecoregions

for (i in ecoregion) {
  
  ## Create frequency of occurrence for each latitudinal bin and frequency class
  
  test<-diversity%>%
    filter(Ecoregion%in%i)%>%
    glimpse()
  n<-as.numeric(nrow(test))
  
  test.1<-test%>%
    dplyr::group_by(Ecoregion,p.PD.q1)%>%
    dplyr::summarise(number=n())%>%
    mutate(percentage=(number/n)*100)%>%
    ungroup()%>%
    glimpse()
  
  PD.q1.rules<-rbind(PD.q1.rules,test.1)
  
}

## (F) PD_q2 ----

## Calculate the relative frequency of each assembly rule - Neutral, Underdispersed, Overdispersed

PD.q2.rules=data.frame()

ecoregion<-as.vector(unique(diversity$Ecoregion)) ## For n in Ecoregions

for (i in ecoregion) {
  
  ## Create frequency of occurrence for each latitudinal bin and frequency class
  
  test<-diversity%>%
    filter(Ecoregion%in%i)%>%
    glimpse()
  n<-as.numeric(nrow(test))
  
  test.1<-test%>%
    dplyr::group_by(Ecoregion,p.PD.q2)%>%
    dplyr::summarise(number=n())%>%
    mutate(percentage=(number/n)*100)%>%
    ungroup()%>%
    glimpse()
  
  PD.q2.rules<-rbind(PD.q2.rules,test.1)
  
}

## Round percentage values to two decimals

FD.q0.rules$percentage<-round(FD.q0.rules$percentage,1)
FD.q1.rules$percentage<-round(FD.q1.rules$percentage,1)
FD.q2.rules$percentage<-round(FD.q2.rules$percentage,1)

PD.q0.rules$percentage<-round(PD.q0.rules$percentage,1)
PD.q1.rules$percentage<-round(PD.q1.rules$percentage,1)
PD.q2.rules$percentage<-round(PD.q2.rules$percentage,1)

## Plot as a stack bar plot

## FD_q0

levels(FD.q0.rules$p.FD.q0)

FD.q0.rules<-FD.q0.rules%>%
  dplyr::mutate(p.FD.q0=fct_relevel(p.FD.q0,"Overdispersed (95%)","Overdispersed (75%)",
                                    "Random","Underdispersed (75%)","Underdispersed (95%)"))%>%
  glimpse()

FD_q0<-ggplot(FD.q0.rules,aes(fill=p.FD.q0, y=percentage, x=Ecoregion)) + 
  ggtitle('(a)')+
  geom_bar(position="stack", stat="identity",colour="black")+
  scale_fill_manual(labels=c("Overdispersed (95%)","Overdispersed (75%)",
                             "Random","Underdispersed (75%)","Underdispersed (95%)"),
                    values = c("firebrick","firebrick2","grey","lightblue","blue"))+
  theme_classic()+
  Theme1+
  theme(legend.position = "right")
FD_q0

## FD_q0

levels(FD.q1.rules$p.FD.q1)

FD.q1.rules<-FD.q1.rules%>%
  dplyr::mutate(p.FD.q1=fct_relevel(p.FD.q1,"Overdispersed (75%)","Random",
                                    "Underdispersed (75%)","Underdispersed (95%)"))%>%
  glimpse()

FD_q1<-ggplot(FD.q1.rules,aes(fill=p.FD.q1, y=percentage, x=Ecoregion)) + 
  ggtitle('(b)')+
  geom_bar(position="stack", stat="identity",colour="black")+
  scale_fill_manual(labels=c("Overdispersed (75%)","Random",
                             "Underdispersed (75%)","Underdispersed (95%)"),
                    values = c("firebrick2","grey","lightblue","blue"))+
  theme_classic()+
  Theme1+
  theme(legend.position = "right")
FD_q1

## FD_q2

levels(FD.q2.rules$p.FD.q2)

FD.q2.rules<-FD.q2.rules%>%
  dplyr::mutate(p.FD.q2=fct_relevel(p.FD.q2,"Overdispersed (75%)","Random",
                                    "Underdispersed (75%)","Underdispersed (95%)"))%>%
  glimpse()

FD_q2<-ggplot(FD.q2.rules,aes(fill=p.FD.q2, y=percentage, x=Ecoregion)) + 
  ggtitle('(c)')+
  geom_bar(position="stack", stat="identity",colour="black")+
  scale_fill_manual(labels=c("Overdispersed (75%)","Random",
                             "Underdispersed (75%)","Underdispersed (95%)"),
                    values = c("firebrick2","grey","lightblue","blue"))+
  theme_classic()+
  Theme1+
  theme(legend.position = "right")
FD_q2

## PD_q0

levels(PD.q0.rules$p.PD.q0)

PD.q0.rules<-PD.q0.rules%>%
  dplyr::mutate(p.PD.q0=fct_relevel(p.PD.q0,"Overdispersed (75%)",
                                    "Random","Underdispersed (75%)","Underdispersed (95%)"))%>%
  glimpse()

PD_q0<-ggplot(PD.q0.rules,aes(fill=p.PD.q0, y=percentage, x=Ecoregion)) + 
  ggtitle('(d)')+
  geom_bar(position="stack", stat="identity",colour="black")+
  scale_fill_manual(labels=c("Overdispersed (75%)",
                             "Random","Underdispersed (75%)","Underdispersed (95%)"),
                    values = c("firebrick2","grey","lightblue","blue"))+
  theme_classic()+
  Theme1+
  theme(legend.position = "right")
PD_q0

## PD_q1

levels(PD.q1.rules$p.PD.q1)

PD.q1.rules<-PD.q1.rules%>%
  dplyr::mutate(p.PD.q1=fct_relevel(p.PD.q1,"Overdispersed (75%)","Random",
                                    "Underdispersed (75%)","Underdispersed (95%)"))%>%
  glimpse()

PD_q1<-ggplot(PD.q1.rules,aes(fill=p.PD.q1, y=percentage, x=Ecoregion)) + 
  ggtitle('(e)')+
  geom_bar(position="stack", stat="identity",colour="black")+
  scale_fill_manual(labels=c("Overdispersed (75%)","Random",
                             "Underdispersed (75%)","Underdispersed (95%)"),
                    values = c("firebrick2","grey","lightblue","blue"))+
  theme_classic()+
  Theme1+
  theme(legend.position = "right")
PD_q1

## PD_q2

levels(PD.q2.rules$p.PD.q2)

PD.q2.rules<-PD.q2.rules%>%
  dplyr::mutate(p.PD.q2=fct_relevel(p.PD.q2,"Overdispersed (75%)",
                                    "Random","Underdispersed (75%)","Underdispersed (95%)"))%>%
  glimpse()

PD_q2<-ggplot(PD.q2.rules,aes(fill=p.PD.q2, y=percentage, x=Ecoregion)) + 
  ggtitle('(f)')+
  geom_bar(position="stack", stat="identity",colour="black")+
  scale_fill_manual(labels=c("Overdispersed (75%)","Random",
                             "Underdispersed (75%)","Underdispersed (95%)"),
                    values = c("firebrick2","grey","lightblue","blue"))+
  theme_classic()+
  Theme1+
  theme(legend.position = "right")
PD_q2

## Arrange plots in a grob

ggarrange(FD_q0,FD_q1,FD_q2,
          PD_q0,PD_q1,PD_q2,
          nrow = 2,ncol = 3,
          align = 'hv',common.legend = T,legend = "bottom")

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Fig3_Assembly_Rules'

ggsave(paste(name,".png",sep="."),width = 19, height = 15,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 19, height = 15,units = "cm",dpi=600,useDingbats=FALSE)

################################################################################################################################
###################################################### (8) LM ############################################################

## Load libraries

library(glmmTMB)
library(mgcv)
library(MuMIn)
citation

## Name project

name<-"NEA_Fishes"

## Bring in diversity dataset

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

dat<-read.csv('diversity.25052021.csv')%>%
  glimpse()

### Check NAs in the data

sum(is.na(dat))/prod(dim(dat))*100
apply(dat,2,function(col)sum(is.na(col))/length(col))*100

## Exclude NAs in the environmental data

dat<-dat%>%
  filter(!is.na(BO_sstmax))%>%
  filter(!is.na(npp_mean))%>%
  glimpse()
n_distinct(dat$Site) # 9 sites missing environmental data

### Check NAs in the data in the metrics

sum(is.na(dat))/prod(dim(dat))*100
apply(dat,2,function(col)sum(is.na(col))/length(col))*100

### Code covariates

glimpse(dat)

dat$Total_area<-as.numeric(dat$Total_area)
dat$pop.den.50<-as.numeric(dat$pop.den.50)
dat$clust.12km<-as.factor(dat$clust.12km)

## Set predictor variables
## For now we will exclude reserve size from the models

names(dat)
pred.vars.cont=c("BO_sstmax","BO_sstmean","BO_sstmin","BO_sstrange","BO2_nitratemax_ss","BO2_nitratemean_ss","BO2_nitratemin_ss",
                 "BO2_nitraterange_ss","BO2_phosphatemax_ss","BO2_phosphatemean_ss","BO2_phosphatemin_ss","BO2_phosphaterange_ss",
                 "npp_mean","npp_min","npp_max","npp_sd","pop.den.50","Depth",
                 "Abutting_regions","Dst2continent","Connec_30m","Shelf.km2","Total_area")

# Plot of likely transformations 

plot.new()

par(mfrow=c(3,2))
for (i in pred.vars.cont) {
  x<-dat[ ,i]
  x = as.numeric(unlist(x))  
  hist((x))#Looks best
  plot((x),main = paste(i))
  hist(sqrt(x))
  plot(sqrt(x))
  hist(log(x+1))
  plot(log(x+1))
}

## Transform predictors

dat$Total_area<-log1p(dat$Total_area)
dat$Shelf.km2<-log1p(dat$Shelf.km2)
dat$Connec_30m<-log1p(dat$Connec_30m)
dat$Connec_200m<-log1p(dat$Connec_200m)
dat$Depth<-log1p(dat$Depth)
dat$pop.den.50<-log1p(dat$pop.den.50)
dat$npp_sd<-log1p(dat$npp_sd)
dat$BO2_nitratemin_ss<-log1p(dat$BO2_nitratemin_ss)
dat$BO2_nitratemean_ss<-log1p(dat$BO2_nitratemean_ss)

## Identify outliers 

plot.new()
par(mfrow=c(1,3))
for (i in pred.vars.cont) {
  x<-dat[ ,i]
  x = as.numeric(unlist(x))  
  hist((x))#Looks best
  plot((x),main = paste(i))
  boxplot(x)
}

## Explore correlations between covariates

library(corrplot)
library(RColorBrewer)

## Visualize

M<-dat[,pred.vars.cont]
M<-round(cor(M),2)

plot.new()
par(mfrow=c(1,1))
corrplot(M,method="number")

# Check for correlation of predictor variables- remove anything highly correlated (>0.70)---

test<-as.data.frame(round(cor(dat[,pred.vars.cont]),2))

## Select the set of predictors - with correlations < 0.8

pred.vars.cont=c("BO_sstmean","BO2_nitratemean_ss","npp_mean","pop.den.50",
                 "Dst2continent","Depth")

## Visualize

M<-dat[,pred.vars.cont]
M<-round(cor(M),2)

plot.new()
par(mfrow=c(1,1))
corrplot(M,method="number")

## Scale predictor variables

pred.vars.cont

dat$BO_sstmean<-scale(dat$BO_sstmean)
dat$BO2_nitratemean_ss<-scale(dat$BO2_nitratemean_ss)
dat$npp_mean<-scale(dat$npp_mean)
dat$pop.den.50<-scale(dat$pop.den.50)
dat$Dst2continent<-scale(dat$Dst2continent)
dat$Depth<-scale(dat$Depth)
dat$Total_area<-scale(dat$Total_area)

### Check normality in response variables

hist(dat$richness.res)
shapiro.test(dat$richness.res)

hist(dat$diversity.q1.res)
shapiro.test(dat$diversity.q1.res)

hist(dat$diversity.q2.res)
shapiro.test(dat$diversity.q2.res)

hist(dat$FD_q0.res)
shapiro.test(dat$FD_q0)

hist(dat$FD_q1.res)
shapiro.test(dat$FD_q1.res)

hist(dat$FD_q2.res)
shapiro.test(dat$FD_q2.res)

hist(dat$PD_q0.res)
shapiro.test(dat$PD_q0.res)

hist(dat$PD_q1.res)
shapiro.test(dat$PD_q1.res)

hist(dat$PD_q2.res)
shapiro.test(dat$PD_q2.res)

#### TDq0  model ----

library(lme4)
citation('lme4')

hist(dat$richness.res)

M1<-  lm(richness.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
           pop.den.50  + Dst2continent + Depth,
           data = dat,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)
qqnorm(resid(M1))

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`30`
test$`26`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/TD')
dir()

write.csv(sel.table,"GLMM_TD_q0_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/TD')
dir()

write.csv(importance.scores,"GLMM_TD_q0_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`30`
test$`26`

M1<-lm(richness.res ~ BO_sstmean + Dst2continent + npp_mean + 1,
       data = dat, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat$TD.q0.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat)<-~Longitude+Latitude
class(dat)

### Now we can set the reference system to the widely used WGS84

proj4string(dat)<-CRS("+init=epsg:4326")
dat@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat$TD.q0.mod.res~1,data=dat,cutoff=100,width=1)
plot(richnes.var,main="(a) Richness model",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat$TD.q0.mod.res,dists.inv)

#### TDq1 model ----

dat<-as.data.frame(dat) ## Reconvert to a dataframe

hist(dat$diversity.q1.res)

M1<-lm(diversity.q1.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
                          pop.den.50  + Dst2continent + Depth,
           data = dat,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`58`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/TD')
dir()

write.csv(sel.table,"GLMM_TD_q1_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/TD')
dir()

write.csv(importance.scores,"GLMM_TDq1_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`58`

M1<-lm(diversity.q1.res ~ BO_sstmean + Dst2continent + 
           npp_mean + pop.den.50 + 1, data = dat, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat$TD.q1.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat)<-~Longitude+Latitude
class(dat)

### Now we can set the reference system to the widely used WGS84

proj4string(dat)<-CRS("+init=epsg:4326")
dat@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat$TD.q1.mod.res~1,data=dat,cutoff=100,width=1)
plot(richnes.var,main="(b) TD_q1",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat$TD.q1.mod.res,dists.inv)

#### TDq2 model ----

dat<-as.data.frame(dat) ## Reconvert to a dataframe

hist(dat$diversity.q2.res)

M1<-  lm(diversity.q2.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
           pop.den.50  + Dst2continent + Depth,
           data = dat,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`58`
test$`50`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/TD')
dir()

write.csv(sel.table,"GLMM_TDq2_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/TD')
dir()

write.csv(importance.scores,"GLMM_TDq2_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`50`

M1<-lm(diversity.q2.res ~ BO_sstmean + npp_mean + pop.den.50 + 
         1, data = dat, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat$TD.q2.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat)<-~Longitude+Latitude
class(dat)

### Now we can set the reference system to the widely used WGS84

proj4string(dat)<-CRS("+init=epsg:4326")
dat@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat$TD.q2.mod.res~1,data=dat,cutoff=100,width=1)
plot(richnes.var,main="(c) TD_q2",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat$TD.q2.mod.res,dists.inv)

#### FDq0 model ----

dat<-as.data.frame(dat) ## Reconvert to a dataframe

## Filter missing values from modelling - 3 sites missing

dat.FD<-dat%>%
  filter(!is.na(FD_q0.res))%>%
  glimpse()

hist(dat.FD$FD_q0.res)

M1<-lm(FD_q0.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
         pop.den.50 + Dst2continent + Depth,
         data = dat.FD,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`57`
test$`59`
test$`45`
test$`61`
test$`29`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/FD')
dir()

write.csv(sel.table,"GLMM_FDq0_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/FD')
dir()
write.csv(importance.scores,"GLMM_FDq0_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`29`

M1<-lm(FD_q0.res ~ Depth + Dst2continent + npp_mean + 1, 
       data = dat.FD, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

# Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat.FD$FD_q0.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat.FD)<-~Longitude+Latitude
class(dat.FD)

### Now we can set the reference system to the widely used WGS84

proj4string(dat.FD)<-CRS("+init=epsg:4326")
dat.FD@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat.FD$FD_q0.mod.res~1,data=dat.FD,cutoff=100,width=1)
plot(richnes.var,main="(d) FD_q0",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat.FD, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat.FD$FD_q0.mod.res,dists.inv)

#### FDq1 model ----

dat.FD<-as.data.frame(dat.FD) ## Reconvert to a dataframe

hist(dat$FD_q1.res)

M1<-lm(FD_q1.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
                   pop.den.50  + Dst2continent + Depth,
           data = dat.FD,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`8`
test$`14`
test$`38`
test$`16`
test$`12`
test$`22`
test$`40`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/FD')
dir()

write.csv(sel.table,"GLMM_FDq1_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/FD')
dir()

write.csv(importance.scores,"GLMM_FDq1_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`40`

M1<-lm(FD_q1.res ~ BO_sstmean + BO2_nitratemean_ss + Depth + 
       pop.den.50 + 1, data = dat.FD, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat.FD$FD_q1.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat.FD)<-~Longitude+Latitude
class(dat.FD)

### Now we can set the reference system to the widely used WGS84

proj4string(dat.FD)<-CRS("+init=epsg:4326")
dat.FD@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat.FD$FD_q1.mod.res~1,data=dat.FD,cutoff=100,width=1)
plot(richnes.var,main="(f) FD_q1",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat.FD, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat.FD$FD_q1.mod.res,dists.inv)

#### FDq2 model ----

dat.FD<-as.data.frame(dat.FD) ## Reconvert to a dataframe

hist(dat.FD$FD_q2.res)

M1<-lm(FD_q2.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
                   pop.den.50  + Dst2continent + Depth,
           data = dat.FD,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection
# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`8`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/FD')
dir()

write.csv(sel.table,"GLMM_FDq2_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/FD')
dir()

write.csv(importance.scores,"GLMM_FDq2_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`24`

M1<-lm(FD_q2.res ~ BO_sstmean + BO2_nitratemean_ss + Depth + 
         npp_mean + 1, data = dat.FD, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat.FD$FD_q2.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat.FD)<-~Longitude+Latitude
class(dat.FD)

### Now we can set the reference system to the widely used WGS84

proj4string(dat.FD)<-CRS("+init=epsg:4326")
dat.FD@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat.FD$FD_q2.mod.res~1,data=dat.FD,cutoff=100,width=1)
plot(richnes.var,main="(f) FD_q2",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat.FD, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat.FD$FD_q2.mod.res,dists.inv)

#### PDq0 model ----

dat<-as.data.frame(dat) ## Reconvert to a dataframe

## Filter NAs in PD - 8 sites missing

dat.PD<-dat%>%
  filter(!is.na(PD_q0.res))%>%
  glimpse()

hist(dat$PD_q0.res)

M1<-lm(PD_q0.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
                   pop.den.50  + Dst2continent + Depth,
                   data = dat.PD,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`40`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/PD')
dir()

write.csv(sel.table,"GLMM_PDq0_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/PD')
dir()

write.csv(importance.scores,"GLMM_PDq0_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`40`

M1<-lm(PD_q0.res ~ BO_sstmean + BO2_nitratemean_ss + Depth + 
         pop.den.50 + 1, data = dat.PD, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat.PD$PD_q0.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat.PD)<-~Longitude+Latitude
class(dat.PD)

### Now we can set the reference system to the widely used WGS84

proj4string(dat.PD)<-CRS("+init=epsg:4326")
dat.PD@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat.PD$PD_q0.mod.res~1,data=dat.PD,cutoff=100,width=1)
plot(richnes.var,main="(g) PD_q0",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat.PD, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat.PD$PD_q0.mod.res,dists.inv)

#### PDq1 model ----

dat.PD<-as.data.frame(dat.PD) ## Reconvert to a dataframe

hist(dat.PD$PD_q1.res)

M1<-lm(PD_q1.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
                   pop.den.50  + Dst2continent + Depth,
           data = dat.PD,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`46`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/PD')
dir()

write.csv(sel.table,"GLMM_PDq1_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/PD')
dir()

write.csv(importance.scores,"GLMM_PDq1_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`46`

M1<-lm(PD_q1.res ~ BO_sstmean + Depth + Dst2continent + 
      pop.den.50 + 1, data = dat.PD, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat.PD$PD_q1.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat.PD)<-~Longitude+Latitude
class(dat.PD)

### Now we can set the reference system to the widely used WGS84

proj4string(dat.PD)<-CRS("+init=epsg:4326")
dat.PD@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat.PD$PD_q1.mod.res~1,data=dat.PD,cutoff=100,width=1)
plot(richnes.var,main="(h) PD_q1",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat.PD, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat.PD$PD_q1.mod.res,dists.inv)

#### PDq2 model ----

dat.PD<-as.data.frame(dat.PD) ## Reconvert to a dataframe

hist(dat$PD_q2.res)

M1<-lm(PD_q2.res ~ BO_sstmean +  BO2_nitratemean_ss + npp_mean + 
                   pop.den.50  + Dst2continent + Depth,
           data = dat.PD,na.action = "na.fail")
summary(M1)

## Check Variance inflation factors - Multicolinearity

library(performance)
check_collinearity(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Run model selection

# only allow a maximum of 4 and minimum of 1 parameters in each model

results<-dredge(M1,m.lim = c(3,4),rank = AICc)

# what's it look like, hmm AIC with small sample bias adjustment AICc
# delta AICc, and the model weights
results

# create a confidence set of models using the subset function
# select models with delta AICc less than 5
# IMPORTANT: Weights have been renormalized!!

subset(results, delta <=2)

# coerce the object out.put into a data frame
# elements 6-10 in out.put have what we want

sel.table<-as.data.frame(subset(results, delta <=2))[8:12]
sel.table

# a little clean-up, lets round things a bit

sel.table[,2:3]<- round(sel.table[,2:3],2)
sel.table[,4:5]<- round(sel.table[,4:5],3)

## lets be sure to put the model names in a column
sel.table$Model<-rownames(sel.table)

test<-get.models(results,subset = delta <= 2)

## Extract top model

test$`42`

# write to a file, here a comma separated values format
# make sure your working directory is properly specified

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/PD')
dir()

write.csv(sel.table,"GLMM_PDq2_Top.csv", row.names = F)

# Importance weights for individual predictor variables
# calculated using the importance function

MuMIn::importance(results) ## Error

importance.scores<-as.data.frame(MuMIn::importance(results))
importance.scores[,1]<- round(importance.scores[,1],2)

importance.scores$Predictor<-rownames(importance.scores)

## Export importance scores

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM/PD')
dir()

write.csv(importance.scores,"GLMM_PDq2_Importance.csv", row.names = F)

## Obtain Model averaged coefficients and SE

# Model average using all candidate models, always use revised.var = TRUE

MA.ests<-model.avg(results, revised.var = TRUE)
summary(MA.ests)

## Check top ranked model

test$`42`

M1<-lm(PD_q2.res ~ BO_sstmean + Dst2continent + pop.den.50 + 
         1, data = dat.PD, na.action = "na.fail")
summary(M1)

## Check model assumptions - 
## Deviations from linearity and heterocedasticity
## Residuals are normally distributed

plot(M1)

## Extract residuals

resid<-resid(M1)

## Join residuals to dataframe

dat.PD$PD_q2.mod.res<-resid

### Check for residual auto-correlation ----

## Convert into an spatial object

coordinates(dat.PD)<-~Longitude+Latitude
class(dat.PD)

### Now we can set the reference system to the widely used WGS84

proj4string(dat.PD)<-CRS("+init=epsg:4326")
dat.PD@proj4string

## Compute semivariogram

library(gstat)

richnes.var<-variogram(dat.PD$PD_q2.mod.res~1,data=dat.PD,cutoff=100,width=1)
plot(richnes.var,main="(i) PD_q2",ylab="Semivariance",xlab="Distance (km)")

### Calculate Moran's I based on distance via the spdep package
### We would calculated manually for each basin, diversity index combination and store it in a csv file
### However - for future reference it would be good to loop all of this together

## Global Moran's I ---- 

library(geosphere)

## Legal

dists <- distm(dat.PD, fun = distGeo)
min(dists) ## Distance of 0 correspond to temporally auto-correlated data
max(dists) 

## We need to generate a matrix of inverse distance weights
### Replace the diagonal with 0

dists.inv<- 1/dists
diag(dists.inv) <- 0

## Remove infinite values in the matrix

dists.inv[is.infinite(dists.inv)] <- 0 ## I am not too sure this step in correct

## Calculate Moran's I test statistic - ape package

library(ape)

## Legal (response)

Moran.I(dat.PD$PD_q2.mod.res,dists.inv)

#########################################################################################################################
##################################### (9) Model-averaged coefficients ##################################################

library(forcats)

## Bring in data

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/ModelOut/GLMM')
dir()

dat<-read.csv('GLMM_Coefficients_Pooled.csv')%>%
  dplyr::mutate(Diversity=fct_relevel(Diversity,'PD (q = 2)','PD (q = 1)','PD (q = 0)',
                                     'FD (q = 2)','FD (q = 1)','FD (q = 0)',
                                     'TD (q = 2)','TD (q = 1)','TD (q = 0)'))%>%
  glimpse()

## Plot model averaged coefficients

unique(dat$Diversity)

## TD

coefficients.TD<-ggplot()+
  xlab('')+
  ggtitle('(a)')+
  geom_point(data=dat%>%filter(Diversity%in%c('TD (q = 0)', 'TD (q = 1)', 'TD (q = 2)')),
             aes(x=Predictor,y=Estimate,shape=Diversity,colour=Diversity),size=3,show.legend = T,
             position=position_dodge(width=0.5))+
  geom_errorbar(data=dat%>%filter(Diversity%in%c('TD (q = 0)', 'TD (q = 1)', 'TD (q = 2)')),
                aes(x=Predictor,ymin=Estimate-SE, ymax=Estimate+SE,colour=Diversity), width=.2,show.legend = F,
                position=position_dodge(width=0.5))+
  scale_color_manual(labels = c("TD (q = 0)", "TD (q = 1)","TD (q = 2)"),values=c("lightgrey","darkgrey","black"))+
  coord_flip()+
  ylim(-0.33,0.3)+
  geom_hline(yintercept = 0,linetype="dashed")+
  theme_classic()+
  Theme1+
  theme(legend.position = "none",
        legend.direction = "horizontal",
        axis.text.y = element_blank())
coefficients.TD

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Coefficients_TD'

ggsave(paste(name,".png",sep="."),width = 8, height = 15,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 8, height = 15,units = "cm",dpi=600,useDingbats=FALSE)

## FD

coefficients.FD<-ggplot()+
  xlab('')+
  ggtitle('(b)')+
  geom_point(data=dat%>%filter(Diversity%in%c('FD (q = 0)', 'FD (q = 1)', 'FD (q = 2)')),
             aes(x=Predictor,y=Estimate,shape=Diversity,colour=Diversity),size=3,show.legend = T,
             position=position_dodge(width=0.5))+
  geom_errorbar(data=dat%>%filter(Diversity%in%c('FD (q = 0)', 'FD (q = 1)', 'FD (q = 2)')),
                aes(x=Predictor,ymin=Estimate-SE, ymax=Estimate+SE,colour=Diversity), width=.2,show.legend = F,
                position=position_dodge(width=0.5))+
  scale_color_manual(labels = c("FD (q = 0)", "FD (q = 1)","FD (q = 2)"),values=c("lightgrey","darkgrey","black"))+
  coord_flip()+
  ylim(-0.33,0.3)+
  geom_hline(yintercept = 0,linetype="dashed")+
  theme_classic()+
  Theme1+
  theme(legend.position = "none",
        legend.direction = "horizontal",
        axis.text.y = element_blank())
coefficients.FD

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Coefficients_FD'

ggsave(paste(name,".png",sep="."),width = 8, height = 15,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 8, height = 15,units = "cm",dpi=600,useDingbats=FALSE)

## PD

coefficients.PD<-ggplot()+
  xlab('')+
  ggtitle('(c)')+
  geom_point(data=dat%>%filter(Diversity%in%c('PD (q = 0)', 'PD (q = 1)', 'PD (q = 2)')),
             aes(x=Predictor,y=Estimate,shape=Diversity,colour=Diversity),size=3,show.legend = T,
             position=position_dodge(width=0.5))+
  geom_errorbar(data=dat%>%filter(Diversity%in%c('PD (q = 0)', 'PD (q = 1)', 'PD (q = 2)')),
                aes(x=Predictor,ymin=Estimate-SE, ymax=Estimate+SE,colour=Diversity), width=.2,show.legend = F,
                position=position_dodge(width=0.5))+
  scale_color_manual(labels = c("PD (q = 0)", "PD (q = 1)","PD (q = 2)"),values=c("lightgrey","darkgrey","black"))+
  coord_flip()+
  ylim(-0.33,0.3)+
  geom_hline(yintercept = 0,linetype="dashed")+
  theme_classic()+
  Theme1+
  theme(legend.position = "none",
        legend.direction = "horizontal")
coefficients.PD

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Coefficients_PD'

ggsave(paste(name,".png",sep="."),width = 8, height = 15,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 8, height = 15,units = "cm",dpi=600,useDingbats=FALSE)

################################################################################################
########################### (10) Demographic stochasticity #####################################

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Raw')
dir()

dat<-read.csv("NEA_analyses.csv")%>%
  mutate(Total_area=Dimensions*Effort)%>%
  dplyr::select(-TotalAbun)%>%
  glimpse()
n_distinct(dat$Site)

## How many sites per Ecoregion
## Minimun number of sites samples per Ecoregion = 17

test<-dat%>%
  group_by(Ecoregion)%>%
  summarise(N=n_distinct(Site))%>%
  glimpse()

## Check variance of species abundances across Ecoregions

## First we need to resample the data to select for each latitudinal bin 4 sites (min)

dataframe=data.frame()

number<-1:999
ecoregion<-as.vector(unique(dat$Ecoregion)) ## For n in 6 Ecoregions

for(j in number) {
  
  for (i in ecoregion) {
    
    ## First convert into wide format 
    
    test<-dat%>%
      dplyr::filter(Ecoregion%in%i)%>%
      dplyr::select(Site,Taxa,response)%>%
      pivot_wider(names_from = "Taxa",values_from = response) %>%
      mutate_all(~replace_na(., 0))%>%
      sample_n(17)%>%
      glimpse()
    
    ## Convert first column
    
    ## Reconvert to long format
    
    test<-test%>%
      pivot_longer(cols = c(-Site), names_to = "Taxa", values_to = "response")%>%
      glimpse()
    
    ## Now get the mean and SD for each species
    
    test.1<-test%>%
      group_by(Taxa)%>%
      summarise(mean=mean(response),
                SD=sd(response))%>%
      glimpse()
    test.1$number<-j
    test.1$Ecoregion<-i
    
    dataframe<-rbind(dataframe,test.1)
    
  }
}

## Export dataframe 

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

write.csv(dataframe,"Variance.species.abundances.csv")

## Bring variance in species abundance dataframe

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Diversity')
dir()

dataframe<-read.csv('Variance.species.abundances.csv')%>%
  glimpse()

## Summarize mean and SD across random draws of sites

## First we can do without accounting for individual species

summary<-dataframe%>%
  group_by(Ecoregion)%>%
  summarise(mean=mean(mean,na.rm=TRUE),
            SD=mean(SD,na.rm = TRUE))%>%
  glimpse()

## Now plot mean and SD across latitudinal bins

library(forcats)

summary<-summary%>%
  mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Webbnesia",
                               "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

ggplot(summary,aes(x=Ecoregion,y=mean))+
  geom_errorbar(aes(ymin=mean-SD,ymax=mean+SD),color = "black",width=.2,size=1)+
  geom_point(size=2)+
  ggtitle('(a) Pooled')+
  coord_flip()+
  theme_classic()+
  theme(axis.text.x = element_text(size=10))

## Explore if variance in species abundance is equal across species from different functional groups

## Bring in corrected traits

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Data/Databases')
dir()

traits<-read.csv("traits.final.csv")%>%
  dplyr::select(-Trophic.group2)%>%
  glimpse()
traits$Taxa<-gsub('\\.', ' ', traits$Taxa)

## Change dot in spp species

dataframe$Taxa<-gsub('\\.', '', dataframe$Taxa)

## Group herbivore functional guilds into Herbivores/Detritivores category

unique(traits$Trophic.group)

traits<-traits%>%
  dplyr::mutate(Trophic.group=ifelse(Trophic.group%in%c('Browsing herbivore','Scraping herbivore',
                                                 'Algal farmer'),"Herbivores/Detritivores",
                                     ifelse(Trophic.group%in%c('Benthic invertivore'),'Benthic invertivore',
                                            ifelse(Trophic.group%in%c('Planktivore'),'Planktivore',
                                                   ifelse(Trophic.group%in%c('Omnivore'),'Omnivore','Higher carnivore')))))%>%
  glimpse()

## See if names have the same format

x<-as.vector(unique(dataframe$Taxa))
y<-as.vector(unique(traits$Taxa))

setdiff(x,y)

## Join traits with taxa in variance dataset

dataframe<-left_join(dataframe,traits,by="Taxa")%>%glimpse()
unique(dataframe$Trophic.group)
sum(is.na(dataframe$Trophic.group))

## Second we can do accounting for individual species

summary.species<-dataframe%>%
  group_by(Ecoregion,Trophic.group,MaxLength,Taxa)%>%
  summarise(mean=mean(mean,na.rm=TRUE),
            SD=mean(SD,na.rm = TRUE))%>%
  glimpse()

summary.species<-summary.species%>%
  mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Webbnesia",
                               "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

## Plot via ggplot for each trophic group individually

unique(summary.species$Trophic.group)

## Plot only the ten species with higher abundance and variance in abundance

n.planktivores<-c('Chromis lubbocki','Paranthias furcifer','Thalassoma pavo','Chromis multilineata',
                  'Similiparma lurida','Chromis limbata','Spicara nigricauda','Myripristis jacobus',
                  'Abudefduf saxatilis','Clepticus africanus')

planktivores<-ggplot()+
  ggtitle('(a) Planktivores')+
  geom_hline(yintercept = 0,linetype="dashed")+
  geom_errorbar(data=summary.species%>%filter(Trophic.group%in%c("Planktivore"))%>%filter(Taxa%in%n.planktivores),
                aes(x=reorder(Taxa,-mean),y=mean,ymin=mean-SD,ymax=mean+SD,colour=Ecoregion),width=.2,size=1,
                position=position_dodge(width=0.5))+
  geom_point(data=summary.species%>%filter(mean>1)%>%filter(Trophic.group%in%c("Planktivore"))%>%filter(Taxa%in%n.planktivores),
             aes(x=reorder(Taxa,-mean),y=mean,colour=Ecoregion),size=2.5,position=position_dodge(width=0.5))+
  scale_colour_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Webbnesia",
                               "South European Atlantic Shelf","Celtic Seas",
                               "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                     "deeppink","dodgerblue1","darkblue"))+
  xlab('')+
  ylab('Variance of species abundances (mean ± SD)')+
  theme_classic()+
  theme(axis.text.y = element_text(size=8))+
  theme(legend.position = "bottom")+
  theme(axis.text.x = element_text(angle = 45,hjust=1,vjust = 1,face="italic",size=8))
planktivores

n.invertivores<-c("Coris atlantica","Ctenolabrus rupestris","Mulloidichthys martinicus","Oblada melanura",
                  "Labrus bergylta","Centrolabrus exoletus","Pagellus spp","Diplodus vulgaris",
                  "Coris julis","Sargocentron hastatum")

benthic.invertivores<-ggplot()+
  ggtitle('(b) Benthic invertivores')+
  geom_hline(yintercept = 0,linetype="dashed")+
  geom_errorbar(data=summary.species%>%filter(Trophic.group%in%c("Benthic invertivore"))%>%filter(Taxa%in%n.invertivores),
                aes(x=reorder(Taxa,-mean),y=mean,ymin=mean-SD,ymax=mean+SD,colour=Ecoregion),width=.2,size=1,
                position=position_dodge(width=0.5))+
  geom_point(data=summary.species%>%filter(mean>0)%>%filter(Trophic.group%in%c("Benthic invertivore"))%>%filter(Taxa%in%n.invertivores),
             aes(x=reorder(Taxa,-mean),y=mean,colour=Ecoregion),size=2.5,position=position_dodge(width=0.5))+
  scale_colour_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Webbnesia",
                                 "South European Atlantic Shelf","Celtic Seas",
                                 "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                       "deeppink","dodgerblue1","darkblue"))+
  xlab('')+
  ylab('Variance of species abundances (mean ± SD)')+
  theme_classic()+
  theme(axis.text.y = element_text(size=8))+
  theme(legend.position = "bottom")+
  theme(axis.text.x = element_text(angle = 45,hjust=1,vjust = 1,face="italic",size=8))
benthic.invertivores

n.carnivores<-c("Lutjanus griseus","Pollachius virens","Serranus spp","Pollachius pollachius",
                "Parapristipoma humile","Cephalopholis taeniops","Virididentex acromegalus",
                "Sphyraena viridensis","Aulostomus strigosus","Platybelone spp")

higher.carnivores<-ggplot()+
  ggtitle('(c) Higher carnivores')+
  geom_hline(yintercept = 0,linetype="dashed")+
  geom_errorbar(data=summary.species%>%filter(Trophic.group%in%c("Higher carnivore"))%>%filter(Taxa%in%n.carnivores),
                aes(x=reorder(Taxa,-mean),y=mean,ymin=mean-SD,ymax=mean+SD,colour=Ecoregion),width=.2,size=1,
                position=position_dodge(width=0.5))+
  geom_point(data=summary.species%>%filter(mean>0)%>%filter(Trophic.group%in%c("Higher carnivore"))%>%filter(Taxa%in%n.carnivores),
             aes(x=reorder(Taxa,-mean),y=mean,colour=Ecoregion),size=2.5,position=position_dodge(width=0.5))+
  scale_colour_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Webbnesia",
                                 "South European Atlantic Shelf","Celtic Seas",
                                 "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                       "deeppink","dodgerblue1","darkblue"))+
  xlab('')+
  ylab('Variance of species abundances (mean ± SD)')+
  theme_classic()+
  theme(axis.text.y = element_text(size=8))+
  theme(legend.position = "bottom")+
  theme(axis.text.x = element_text(angle = 45,hjust=1,vjust = 1,face="italic",size=8))
higher.carnivores

n.omnivores<-c("Canthigaster capistrata","Diplodus prayensis","Diplodus fasciatus","Thalassoma newtoni",
               "Diplodus lineatus","Cantherhines pullus","Abudefduf hoefleri","Canthigaster supramacula",
               "Chelon labrosus","Stephanolepis hispidus")

omnivores<-ggplot()+
  ggtitle('(d) Omnivores')+
  geom_hline(yintercept = 0,linetype="dashed")+
  geom_errorbar(data=summary.species%>%filter(Trophic.group%in%c("Omnivore"))%>%filter(Taxa%in%n.omnivores),
                aes(x=reorder(Taxa,-mean),y=mean,ymin=mean-SD,ymax=mean+SD,colour=Ecoregion),width=.2,size=1,
                position=position_dodge(width=0.5))+
  geom_point(data=summary.species%>%filter(mean>0)%>%filter(Trophic.group%in%c("Omnivore"))%>%filter(Taxa%in%n.omnivores),
             aes(x=reorder(Taxa,-mean),y=mean,colour=Ecoregion),size=2.5,position=position_dodge(width=0.5))+
  scale_colour_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Webbnesia",
                                 "South European Atlantic Shelf","Celtic Seas",
                                 "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                       "deeppink","dodgerblue1","darkblue"))+
  xlab('')+
  ylab('Variance of species abundances (mean ± SD)')+
  theme_classic()+
  theme(axis.text.y = element_text(size=8))+
  theme(legend.position = "bottom")+
  theme(axis.text.x = element_text(angle = 45,hjust=1,vjust = 1,face="italic",size=8))
omnivores

n.herbivores<-c("Stegastes spp","Sparisoma cretense","Microspathodon frontatus","Sarpa salpa",
                "Acanthurus monroviae","Sparisoma choati","Kyphosus spp","Prionurus biafraensis",
                "Stegastes imbricatus","Kyphosus sectatrix")

herbivores<-ggplot()+
  ggtitle('(e) Herbivores/Detritivores')+
  geom_hline(yintercept = 0,linetype="dashed")+
  geom_errorbar(data=summary.species%>%filter(Trophic.group%in%c("Herbivores/Detritivores"))%>%filter(Taxa%in%n.herbivores),
                aes(x=reorder(Taxa,-mean),y=mean,ymin=mean-SD,ymax=mean+SD,colour=Ecoregion),width=.2,size=1,
                position=position_dodge(width=0.5))+
  geom_point(data=summary.species%>%filter(mean>0)%>%filter(Trophic.group%in%c("Herbivores/Detritivores"))%>%filter(Taxa%in%n.herbivores),
             aes(x=reorder(Taxa,-mean),y=mean,colour=Ecoregion),size=2.5,position=position_dodge(width=0.5))+
  scale_colour_manual(labels = c("Gulf of Guinea Islands", "Cape Verde","Webbnesia",
                                 "South European Atlantic Shelf","Celtic Seas",
                                 "North Sea"),values=c("darkgreen", "darkorange","chocolate4",
                                                       "deeppink","dodgerblue1","darkblue"))+
  xlab('')+
  ylab('Variance of species abundances (mean ± SD)')+
  theme_classic()+
  theme(axis.text.y = element_text(size=8))+
  theme(legend.position = "bottom")+
  theme(axis.text.x = element_text(angle = 45,hjust=1,vjust = 1,face="italic",size=8))
herbivores

## Arrange plots in a grob

ggarrange(planktivores,benthic.invertivores,higher.carnivores,omnivores,herbivores,
          nrow = 2,ncol = 3,align = 'hv',common.legend = T,legend = "none")

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Appendix_FigA7_Species_Abundance_Variance'

ggsave(paste(name,".png",sep="."),width = 21, height = 15,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 21, height = 15,units = "cm",dpi=600,useDingbats=FALSE)

## We can also plot the mean variance and SD variance across species in each group

summary.sd<-summary.species%>%
  group_by(Ecoregion,Trophic.group)%>%
  summarise(mean_SD=mean(SD),
            sd_SD=sd(SD))%>%
  glimpse()

summary.sd<-summary.sd%>%
  mutate(Ecoregion=fct_relevel(Ecoregion,"Gulf of Guinea Islands","Cape Verde","Webbnesia",
                               "South European Atlantic Shelf","Celtic Seas","North Sea"))%>%
  glimpse()

## Plot for each trophic group

unique(summary.sd$Trophic.group)

ggplot()+
  geom_errorbar(data=summary.sd%>%filter(!is.na(Trophic.group)),
                aes(x=Ecoregion,ymin=mean_SD-sd_SD,ymax=mean_SD+sd_SD),colour='darkgrey',width=.2,size=1)+
  geom_point(data=summary.sd%>%filter(!is.na(Trophic.group)),
             aes(x=Ecoregion,y=mean_SD,fill=Trophic.group),colour="black",size=4.5)+
  geom_point(data=summary.sd%>%filter(!is.na(Trophic.group)),
             aes(x=Ecoregion,y=mean_SD,colour=Trophic.group),size=4)+
  scale_colour_manual(labels=c("Benthic invertivore","Herbivores/Detritivores","Higher carnivore",
                             "Omnivore","Planktivore"),
                    values=c("gold1","forestgreen","firebrick","palegoldenrod","midnightblue"))+
  facet_wrap(~Trophic.group,nrow=1)+
  xlab('')+
  ylab('Variance in species abundances (mean ± SD)')+
  coord_flip()+
  theme_classic()+
  Theme1+
  theme(legend.position = "bottom")

## We can also model this across latitude - taking the median latitude per ecoregion

ecoregion.lat<-dat%>%
  group_by(Ecoregion)%>%
  summarise(Latitude=median(Latitude))%>%
  glimpse()

summary.species<-left_join(summary.species,ecoregion.lat,by="Ecoregion")%>%glimpse()

## Run a gam model per Trophic group

## Create individual dataframes for each species group

unique(summary.species$Trophic.group)

planktivores<-summary.species%>%filter(Trophic.group%in%c('Planktivore'))%>%glimpse()
benthic.invertivores<-summary.species%>%filter(Trophic.group%in%c('Benthic invertivore'))%>%glimpse()
higher.carnivores<-summary.species%>%filter(Trophic.group%in%c('Higher carnivore'))%>%glimpse()
omnivores<-summary.species%>%filter(Trophic.group%in%c('Omnivore'))%>%glimpse()
herbivores<-summary.species%>%filter(Trophic.group%in%c('Herbivores/Detritivores'))%>%glimpse()

## Explore correlations between latitude and MaxLength for each trophic group

cor(planktivores$Latitude,planktivores$MaxLength)
cor(benthic.invertivores$Latitude,benthic.invertivores$MaxLength)
cor(higher.carnivores$Latitude,higher.carnivores$MaxLength)
cor(omnivores$Latitude,omnivores$MaxLength)
cor(herbivores$Latitude,herbivores$MaxLength)


## (A) Planktivores ----

library(mgcViz)

hist(planktivores$SD)

gam<-gam(SD ~ s(Latitude,k=4,bs="cr") + s(MaxLength,k=4,bs="cr"),family=tw(),data = planktivores)
summary(gam)

plot(gam,pages=1,all.terms=TRUE)

## Check gam

plot.new()
par(mfrow=c(2,2))

gam.check(gam)

## Predict to a new dataframe

## Latitude

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(Latitude = seq(min(planktivores$Latitude),max(planktivores$Latitude), length = 100),
                    MaxLength=mean(gam$model$MaxLength),
                    Trophic.group="Planktivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Planktivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Planktivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Planktivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

planktivores.latitude<-ggplot()+
  geom_line(data=La.predicts.Planktivore,aes(x=Latitude,y=response),colour="midnightblue",size=1)+
  geom_line(data=La.predicts.Planktivore,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="midnightblue",size=1,alpha=1)+
  geom_line(data=La.predicts.Planktivore,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="midnightblue",size=1,alpha=1)+
  ggtitle('(a) Planktivores')+
  ylab('Variance in species abundances')+
  xlab('Latitude (°)')+
  theme_classic()+
  #ylim(0,150)+
  Theme1
planktivores.latitude

## MaxLength

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(MaxLength = seq(min(planktivores$MaxLength),max(planktivores$MaxLength), length = 100),
                    Latitude = mean(gam$model$Latitude),
                    Trophic.group="Planktivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Planktivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,MaxLength)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Planktivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Planktivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

planktivores.length<-ggplot()+
  geom_line(data=La.predicts.Planktivore,aes(x=MaxLength,y=response),colour="midnightblue",size=1)+
  geom_line(data=La.predicts.Planktivore,aes(x=MaxLength,y=response - se.fit),linetype="dashed",colour="midnightblue",size=1,alpha=1)+
  geom_line(data=La.predicts.Planktivore,aes(x=MaxLength,y=response + se.fit),linetype="dashed",colour="midnightblue",size=1,alpha=1)+
  ggtitle('(e)')+
  ylab('Variance in species abundances')+
  xlab('Body-size (MaxLength, cm)')+
  theme_classic()+
  #ylim(0,150)+
  Theme1
planktivores.length

## (B) Benthic invertivores ----

hist(benthic.invertivores$SD)

gam<-gam(SD ~ s(Latitude,k=4,bs="cr") + s(MaxLength,k=4,bs="cr"),family=tw(),data = benthic.invertivores)
summary(gam)

plot(gam,pages=1,all.terms=TRUE)

## Check gam

plot.new()
par(mfrow=c(2,2))

gam.check(gam)

## Predict to a new dataframe

## Latitude

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(Latitude = seq(min(benthic.invertivores$Latitude),max(benthic.invertivores$Latitude), length = 100),
                    MaxLength=mean(gam$model$MaxLength),
                    Trophic.group="Benthic invertivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Benthic.invertivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Benthic.invertivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Benthic.invertivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

benthic.invertivores.latitude<-ggplot()+
  geom_line(data=La.predicts.Benthic.invertivore,aes(x=Latitude,y=response),colour="gold1",size=1)+
  geom_line(data=La.predicts.Benthic.invertivore,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="gold1",size=1,alpha=1)+
  geom_line(data=La.predicts.Benthic.invertivore,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="gold1",size=1,alpha=1)+
  ggtitle('(b) Benthic invertivores')+
  ylab('')+
  xlab('Latitude (°)')+
  #ylim(0,150)+
  theme_classic()+
  Theme1
benthic.invertivores.latitude

## MaxLength

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(MaxLength = seq(min(benthic.invertivores$MaxLength),max(benthic.invertivores$MaxLength), length = 100),
                    Latitude = mean(gam$model$Latitude),
                    Trophic.group="Benthic invertivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Benthic.invertivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,MaxLength)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Benthic.invertivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Benthic.invertivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

benthic.invertivores.length<-ggplot()+
  geom_line(data=La.predicts.Benthic.invertivore,aes(x=MaxLength,y=response),colour="gold1",size=1)+
  geom_line(data=La.predicts.Benthic.invertivore,aes(x=MaxLength,y=response - se.fit),linetype="dashed",colour="gold1",size=1,alpha=1)+
  geom_line(data=La.predicts.Benthic.invertivore,aes(x=MaxLength,y=response + se.fit),linetype="dashed",colour="gold1",size=1,alpha=1)+
  ggtitle('(f)')+
  ylab('')+
  xlab('Body-size (MaxLength, cm)')+
  #ylim(0,150)+
  theme_classic()+
  Theme1
benthic.invertivores.length

## (C) Higher carnivores ----

hist(higher.carnivores$SD)

gam<-gam(SD ~ s(Latitude,k=4,bs="cr") + s(MaxLength,k=4,bs="cr"),family=tw(),data = higher.carnivores)
summary(gam)

plot(gam,pages=1,all.terms=TRUE)

## Check gam

plot.new()
par(mfrow=c(2,2))

gam.check(gam)

## Predict to a new dataframe

## Latitude

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(Latitude = seq(min(higher.carnivores$Latitude),max(higher.carnivores$Latitude), length = 100),
                    MaxLength=mean(gam$model$MaxLength),
                    Trophic.group="Higher carnivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Higher.carnivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Higher.carnivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Higher.carnivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

higher.carnivores.latitude<-ggplot()+
  geom_line(data=La.predicts.Higher.carnivore,aes(x=Latitude,y=response),colour="firebrick",size=1)+
  geom_line(data=La.predicts.Higher.carnivore,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="firebrick",size=1,alpha=1)+
  geom_line(data=La.predicts.Higher.carnivore,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="firebrick",size=1,alpha=1)+
  ggtitle('(c) Higher carnivores')+
  ylab('')+
  xlab('Latitude (°)')+
  #ylim(0,150)+
  theme_classic()+
  Theme1
higher.carnivores.latitude

## MaxLength

## Predict and store for plotting

pdat <- expand.grid(MaxLength = seq(min(higher.carnivores$MaxLength),max(higher.carnivores$MaxLength), length = 100),
                    Latitude = mean(gam$model$Latitude),
                    Trophic.group="Higher carnivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Higher.carnivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,MaxLength)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Higher.carnivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Higher.carnivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

higher.carnivores.length<-ggplot()+
  geom_line(data=La.predicts.Higher.carnivore,aes(x=MaxLength,y=response),colour="firebrick",size=1)+
  geom_line(data=La.predicts.Higher.carnivore,aes(x=MaxLength,y=response - se.fit),linetype="dashed",colour="firebrick",size=1,alpha=1)+
  geom_line(data=La.predicts.Higher.carnivore,aes(x=MaxLength,y=response + se.fit),linetype="dashed",colour="firebrick",size=1,alpha=1)+
  ggtitle('(g)')+
  ylab('')+
  xlab('Body-size (MaxLength, cm)')+
  #ylim(0,150)+
  theme_classic()+
  Theme1
higher.carnivores.length

## (D) Omnivores ----

hist(omnivores$SD)

gam<-gam(SD ~ s(Latitude,k=4,bs="cr") + s(MaxLength,k=4,bs="cr"),family=tw(),data = omnivores)
summary(gam)

plot(gam,pages=1,all.terms=TRUE)

## Check gam

plot.new()
par(mfrow=c(2,2))

gam.check(gam)

## Predict to a new dataframe

## Latitude

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(Latitude = seq(min(omnivores$Latitude),max(omnivores$Latitude), length = 100),
                    MaxLength=mean(gam$model$MaxLength),
                    Trophic.group="Omnivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Omnivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Omnivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Omnivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

omnivores.latitude<-ggplot()+
  geom_line(data=La.predicts.Omnivore,aes(x=Latitude,y=response),colour="palegoldenrod",size=1)+
  geom_line(data=La.predicts.Omnivore,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="palegoldenrod",size=1,alpha=1)+
  geom_line(data=La.predicts.Omnivore,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="palegoldenrod",size=1,alpha=1)+
  ggtitle('(d)')+
  #ylim(0,150)+
  ylab('')+
  xlab('Latitude (°)')+
  theme_classic()+
  Theme1
omnivores.latitude

## MaxLength

## Predict and store for plotting

glimpse(summary.species)

pdat <- expand.grid(MaxLength = seq(min(omnivores$MaxLength),max(omnivores$MaxLength), length = 100),
                    Latitude = mean(gam$model$Latitude),
                    Trophic.group="Omnivore")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Omnivore = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,MaxLength)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Omnivore,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Omnivore<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

omnivores.length<-ggplot()+
  geom_line(data=La.predicts.Omnivore,aes(x=MaxLength,y=response),colour="palegoldenrod",size=1)+
  geom_line(data=La.predicts.Omnivore,aes(x=MaxLength,y=response - se.fit),linetype="dashed",colour="palegoldenrod",size=1,alpha=1)+
  geom_line(data=La.predicts.Omnivore,aes(x=MaxLength,y=response + se.fit),linetype="dashed",colour="palegoldenrod",size=1,alpha=1)+
  ggtitle('(g)')+
  #ylim(0,150)+
  ylab('')+
  xlab('Body-size (MaxLength, cm)')+
  theme_classic()+
  Theme1
omnivores.length

## (E) Herbivores ----

hist(herbivores$SD)

gam<-gam(SD ~ s(Latitude,k=4,bs="cr") + s(MaxLength,k=4,bs="cr"),family=tw(),data = herbivores)
summary(gam)

plot(gam,pages=1,all.terms=TRUE)

## Check gam

plot.new()
par(mfrow=c(2,2))

gam.check(gam)

## Predict to a new dataframe

## Latitude

## Predict and store for plotting

pdat <- expand.grid(Latitude = seq(min(herbivores$Latitude),max(herbivores$Latitude), length = 100),
                    MaxLength=mean(gam$model$MaxLength),
                    Trophic.group="Herbivores/Detritivores")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Herbivores.Detritivores = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,Latitude)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Herbivores.Detritivores,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Herbivores.Detritivores<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

herbivores.latitude<-ggplot()+
  geom_line(data=La.predicts.Herbivores.Detritivores,aes(x=Latitude,y=response),colour="forestgreen",size=1)+
  geom_line(data=La.predicts.Herbivores.Detritivores,aes(x=Latitude,y=response - se.fit),linetype="dashed",colour="forestgreen",size=1,alpha=1)+
  geom_line(data=La.predicts.Herbivores.Detritivores,aes(x=Latitude,y=response + se.fit),linetype="dashed",colour="forestgreen",size=1,alpha=1)+
  ggtitle('(e)')+
  #ylim(0,150)+
  ylab('')+
  xlab('Latitude (°)')+
  theme_classic()+
  Theme1
herbivores.latitude

## MaxLength

## Predict and store for plotting

pdat <- expand.grid(MaxLength = seq(min(herbivores$MaxLength),max(herbivores$MaxLength), length = 100),
                    Latitude = mean(gam$model$Latitude),
                    Trophic.group="Herbivores/Detritivores")%>%
  glimpse()

xp <- predict(gam, newdata = pdat,type = 'response',se.fit = T)

La.predicts.Herbivores.Detritivores = pdat%>%data.frame(xp)%>%
  group_by(Trophic.group,MaxLength)%>% #only change here
  dplyr::summarise(response=mean(fit),se.fit=mean(se.fit))%>%
  ungroup()%>%
  glimpse()
write.csv(La.predicts.Herbivores.Detritivores,"predicts.csv") #there is some BUG in dplyr - that this fixes
La.predicts.Herbivores.Detritivores<-read.csv("predicts.csv")%>%
  glimpse()

## Plot via ggplot

herbivores.length<-ggplot()+
  geom_line(data=La.predicts.Herbivores.Detritivores,aes(x=MaxLength,y=response),colour="forestgreen",size=1)+
  geom_line(data=La.predicts.Herbivores.Detritivores,aes(x=MaxLength,y=response - se.fit),linetype="dashed",colour="forestgreen",size=1,alpha=1)+
  geom_line(data=La.predicts.Herbivores.Detritivores,aes(x=MaxLength,y=response + se.fit),linetype="dashed",colour="forestgreen",size=1,alpha=1)+
  ggtitle('(h)')+
  #ylim(0,150)+
  ylab('')+
  xlab('Latitude (°)')+
  theme_classic()+
  Theme1
herbivores.length

## Arrange plots in a grob

ggarrange(planktivores.latitude,benthic.invertivores.latitude,higher.carnivores.latitude,omnivores.latitude,herbivores.latitude,
          planktivores.length,benthic.invertivores.length,higher.carnivores.length,omnivores.length,herbivores.length,
          nrow = 2,ncol = 5,align = 'hv')

## Export plot

setwd('C:/Users/22373243/Dropbox/Projects/Analysis/Analysis_Diversity_Fishes_NE_Atlantic/Plots/JEBG_Revisions')
dir()

name<-'Fig5_Variance_species_abundance_model_01062021'

ggsave(paste(name,".png",sep="."),width = 21, height = 15,units = "cm",dpi=600)
ggsave(paste(name,".pdf",sep="."),width = 21, height = 15,units = "cm",dpi=600,useDingbats=FALSE)

## Supplementary table

glimpse(dataframe)

test<-dataframe%>%
  group_by(Trophic.group,Ecoregion)%>%
  summarise(S=n_distinct(Taxa),
            Mean=mean(mean),
            SD=sd(mean))%>%
  glimpse()
