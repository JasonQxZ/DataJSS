
Hard<-function(t=c(0,0), k=-1, lam=1)
{  y<-t
   t<-abs(t)

   if(k > 0)
   { lam<-sort(t, decreasing=TRUE)[k] }

   y[t<lam]<-0
   return(y)
}


# Soft thresholding function----------------------------------

Soft<-function(t=c(0,0), k=-1, lam=1)
{
   d<-abs(t)

   if(k > 0)
   { lam<- sort(d, decreasing=TRUE)[k+1] }

   if(k >= length(t))
   { lam<- 0 }

   y<- (d-lam)
   y[y<0]<-0
   y<- y * sign(t)
   return(y)
}



# SCAD thresholding function----------------------------------

SCAD<-function(t=c(0,0), k=-1, nv=3.7, lam=1, kappa=1)
{
   d<-abs(t)

   if(k > 0)
   { lam<- sort(d, decreasing=TRUE)[k+1]  / kappa }

   if(k >= length(t))
   { lam<- 0 }

   y<-rep(0, length(t))

    in_1<-  d >= kappa*lam   &  d <  (kappa + 1 )*lam
    in_2<-  (kappa+1)*lam <= d  & d < nv*lam
    in_3<-  d >= nv*lam


    y[in_3]<- t[in_3]

    if( nv-1 < kappa && kappa <= nv )
   {
      in_12<-in_1 | in_2
      y[in_12] <-   sign(t[in_12]) * (d[in_12] - (kappa* lam))
    }

   if( kappa <= nv-1 )
  {
    y[in_1]<-  sign(t[in_1]) * (d[in_1] - (kappa* lam))
    y[in_2]<-  ((nv-1)*t[in_2] - kappa * nv * lam * sign(t[in_2])) / (nv- kappa -1)
   }

    return(y)
}




# A: p*n,  a: n*1-------------------------------

Fmt<-function(A, a, rr=5)
{
  pp<-dim(A)[1];  r<-pp/rr

  b<- matrix(0, nrow=pp, ncol=1)

  for(i in 1:rr )
  {
   b[((i-1) * r +1) : (i*r)] <- A[ ((i-1) * r +1) : (i*r), ] %*% a
  }

return(b)
}



# log-likelihood function-------------------------

lh<-function(Y, X, beta, sig=1, tag="N")
{
  X<-as.matrix(X)
  dx<-dim(X);  n<-dx[1];  p<-dx[2]

  ind_0<-(1:p)[beta != 0]

  bc_0<- beta[ind_0]
  bc_0<-as.matrix(bc_0, ncol=1)

  Xs_0<-X[, ind_0]

  R_0<- Xs_0 %*% bc_0

  if(tag=="N")
  { R_1 <- R_0^2 /2    }

  if(tag=="B")
  { R_1 <- log(1 + exp(R_0) ) }

  if(tag=="P")
  { R_1 <- exp(R_0) }

  ll<- sum( (Y*R_0 -  R_1)/sig^2 )

  if(tag=="P")
  ll<- sum( dpois(Y, R_1, log = TRUE) )

  return(ll)

}



# function for u check------------------------------

Uh<-function(A, uh, b0, b1, tag="N")
 {
   if(tag != "P")
  {
   if(tag=="N")
   { rho<-1 }

   if(tag=="B")
   { rho<- 0.25 }

    bb<-b1-b0
    in_b<- (1:length(bb))[bb != 0]

    bt<-0

    if(length(in_b) != 0)
    {
     bt<- bb[in_b]
     bt<- as.matrix(bt, ncol=1)
     }

    tm1 <- sum(bt^2) / uh
    tm2 <- sum((A[,in_b]%*%bt)^2) * rho

    Bt <- exp(tm1 - tm2)
   }

   if(tag=="P")
    {
     theta_0<-0; theta_1<-0

     in_b0<- (1:length(b0))[b0 != 0]
     in_b1<- (1:length(b1))[b1 != 0]

      if( length(in_b0) !=0)
     {
      bt0<- b0[in_b0];  bt0<- as.matrix(bt0, ncol=1)
      theta_0<- A[,in_b0] %*% bt0
      }

      if( length(in_b1) !=0)
      {
       bt1<- b1[in_b1];  bt1<- as.matrix(bt1, ncol=1)
       theta_1<- A[,in_b1] %*% bt1
      }

      theta_t<- pmax(theta_0, theta_1)

      bb<- b1-b0
      in_b<- (1:length(bb))[bb != 0]

      bt<-0

      if( length(in_b) != 0)
      { bt<- bb[in_b];  bt<- as.matrix(bt, ncol=1) }

      tm1 <-  sum(bt^2) / uh
      tm2 <-  sum( exp(theta_t) * (theta_0 - theta_1)^2 )

      Bt <- exp(tm1 - tm2)
    }

    return(Bt)
 }


########################
# Forward screening
#########################

FR<-function(Y, X, rr=5, k=20)
{
  dX<-dim(X);  n<-dX[1]; p<-dX[2]
  R2<-  Fmt(A=t(X), a=Y, rr=rr)

  index_max<- (1:p)[R2==max(R2)]
  X_s<-X[, index_max]

for(j in 1:(k-1))
{
  X_test<-matrix(0, nrow=n, ncol=j+1)
  X_test[, 1:j]<- X_s
  X_f<-X[,-index_max]

  RSS_test<-rep(0, (p-j))

  for(i in 1 : (p-j) )
  {
    X_test[, j+1]<- X_f[,i]

    b_temp<-solve(t(X_test) %*% X_test, t(X_test) %*% Y)
    RSS_test[i] <-sum(( Y - (X_test %*% b_temp) )^2)
   }

  index_test<- (1: (p-j) )[ RSS_test == min(RSS_test) ]

  X_test[, j+1]<- X_f[,index_test]
  X_s<-X_test
  index_max<- match(X_s[1,], X[1,])

}

return( sort(index_max) )

}



###################################
## X: n*p;  Y: n*1---------------
###################################

AHT<-function(Y, X, beta0, k=20, rr=5, T=500, U=1, er=10^(-3), tag="N")
{

 # initializing------------------------------

 dX<-dim(X);  n<-dX[1]; p<-dX[2]
 X_t<-t(X);

 ind_0<- (1:p)[beta0 != 0]

 # Case if beta0==0--------------------------

 if(length(ind_0) == 0 )
 {
   R_0<-matrix(0, ncol=1, nrow=n)

   if(tag=="B")
   { R_0<- exp(R_0) / (1+exp(R_0) ) }

    if(tag=="P")
   { R_0<- exp(R_0) }


   V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)
   beta1<- Hard(t=V_0, k=k)

   ind_1<- (1:p)[beta1 != 0]
   Xs_1<-X[, ind_1]
   tau_1 <- svd(Xs_1)$d[1]

   ############################
    uu<-  U/ tau_1^2
   #############################
  }

 # Case if beta0!=0-----------------------

 if(length(ind_0) != 0 )
 {
   bc_0<- beta0[ind_0]
   bc_0<- as.matrix(bc_0, ncol=1)

   Xs_0<-X[, ind_0]

   R_0<- Xs_0 %*% bc_0

   if(tag=="B")
   { R_0<- exp(R_0) / (1+exp(R_0) ) }

   if(tag=="P")
   { R_0<- exp(R_0) }

    V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)

   tau_0 <- svd(Xs_0)$d[1]

   ############################
    uu<-  U/ tau_0^2
   #############################
 }


# iteration start---------------------------

   u_c <- uu
   i<-1

repeat{

   repeat
      {
        gamma0<- beta0 + uu * V_0
        beta1<- Hard(t=gamma0, k=k)

        ########## u-check #################
         ucheck<- Uh(A=X, uh=uu, b0=beta0, b1=beta1, tag=tag)

         if( ucheck >= 1 )
         {break}else{ uu <- 0.5 * uu}

        ####################################

      }

      ######## convergence check ##############

        MSE<- sqrt(sum((beta1-beta0)^2))
        if( (i>T) ||  (MSE < er) ){break}

      #########################################

      beta0<-beta1
      ind_0<- (1:p)[beta0 != 0]

      bc_0<- beta0[ind_0]
      bc_0<-as.matrix(bc_0, ncol=1)
      Xs_0<-X[, ind_0]

      R_0<- Xs_0 %*% bc_0

      if(tag=="B")
      { R_0<- exp(R_0) / (1+exp(R_0) ) }

      if(tag=="P")
      { R_0<- exp(R_0) }

      V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)

      uu<-u_c
      i<-i+1

  }

 index<- (1:p)[beta1 != 0 ]

list(index=index, B=bc_0, step=i)
}


AHT_acc<-function(Y, X, beta0, k=20, rr=5, T=500, U=1, er=10^(-3), tag="N")
{
  
  # initializing------------------------------
  
  dX<-dim(X);  n<-dX[1]; p<-dX[2]
  X_t<-t(X);
  
  ind_0<- (1:p)[beta0 != 0]
  
  # Case if beta0==0--------------------------
  
  if(length(ind_0) == 0 )
  {
    R_0<-matrix(0, ncol=1, nrow=n)
    
    if(tag=="B")
    { R_0<- exp(R_0) / (1+exp(R_0) ) }
    
    if(tag=="P")
    { R_0<- exp(R_0) }
    
    
    V_0<-X_t%*%(Y-R_0)
    beta1<- Hard(t=V_0, k=k)
    
    ind_1<- (1:p)[beta1 != 0]
    Xs_1<-X[, ind_1]
    tau_1 <- svd(Xs_1)$d[1]
    
    ############################
    uu<-  U/ tau_1^2
    #############################
  }
  
  # Case if beta0!=0-----------------------
  
  if(length(ind_0) != 0 )
  {
    bc_0<- beta0[ind_0]
    bc_0<- as.matrix(bc_0, ncol=1)
    
    Xs_0<-X[, ind_0]
    
    R_0<- Xs_0 %*% bc_0
    
    if(tag=="B")
    { R_0<- exp(R_0) / (1+exp(R_0) ) }
    
    if(tag=="P")
    { R_0<- exp(R_0) }
    
    V_0<-X_t%*%(Y-R_0)
    
    tau_0 <- svd(Xs_0)$d[1]
    
    ############################
    uu<-  U/ tau_0^2
    #############################
  }
  
  
  # iteration start---------------------------
  
  u_c <- uu
  i<-1
  
  repeat{
    
    repeat
    {
      gamma0<- beta0 + uu * V_0
      beta1<- Hard(t=gamma0, k=k)
      
      ########## u-check #################
      
      ucheck<- Uh(A=X, uh=uu, b0=beta0, b1=beta1, tag=tag)
      
      if( ucheck >= 1 )
      {break}else{ uu <- 0.5 * uu}
      
      ####################################
      
    }
    
    ######## convergence check ##############
    
    MSE<- sqrt(sum((beta1-beta0)^2))
    if( (i>T) ||  (MSE < er) ){break}
    
    #########################################
    
    beta0<-beta1
    ind_0<- (1:p)[beta0 != 0]
    
    bc_0<- beta0[ind_0]
    bc_0<-as.matrix(bc_0, ncol=1)
    Xs_0<-X[, ind_0]
    
    R_0<- Xs_0 %*% bc_0
    
    if(tag=="B")
    { R_0<- exp(R_0) / (1+exp(R_0) ) }
    
    if(tag=="P")
    { R_0<- exp(R_0) }
    
    V_0<-X_t%*%(Y-R_0)
    
    uu<-u_c
    i<-i+1
    
  }
  
  index<- (1:p)[beta1 != 0 ]
  
  list(index=index, B=bc_0, step=i)
}



SCAD_fit<-function(Y, X, beta0, k=20, lam=1, rr=5, T=500, U=1, er=10^(-3), tag="N")
{

 # initializing------------------------------

  dX<-dim(X);  n<-dX[1]; p<-dX[2]
  X_t<-t(X);


   beta0 <- as.matrix(beta0, ncol=1)
   R_0 <- X %*% beta0

   if(tag=="B")
   { R_0<- exp(R_0) / (1+exp(R_0) ) }

   if(tag=="P")
   { R_0<- exp(R_0) }

    V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)

    tau_0 <- svd(X)$d[1]

   ############################
    uu<-  U/ tau_0^2
   ############################


# iteration start---------------------------

   u_c <- uu
   i<-1

repeat{

   repeat
      {
        gamma0<- beta0 + uu * V_0
        beta1<- SCAD(t=gamma0, k=k, lam=lam)

        ########## u-check #################

         ucheck<- Uh(A=X, uh=uu, b0=beta0, b1=beta1, tag=tag)

         if( ucheck >= 1 )
         {break}else{ uu <- 0.5 * uu}

        ####################################

      }

      ######## convergence check ##############

        MSE<- sqrt(sum((beta1-beta0)^2))
        if( (i>1) && ((i>T) || (MSE < er)) ){break}

      #########################################

      beta0<-beta1
      ind_0<- (1:p)[beta0 != 0]

      bc_0<- beta0[ind_0]
      bc_0<-as.matrix(bc_0, ncol=1)
      Xs_0<-X[, ind_0]

      R_0<- Xs_0 %*% bc_0

      if(tag=="B")
      { R_0<- exp(R_0) / (1+exp(R_0) ) }

      if(tag=="P")
      { R_0<- exp(R_0) }

      V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)

      uu<-u_c
      i<-i+1

  }

 index<- (1:p)[beta1 != 0 ]

list(index=index, B=bc_0, step=i)
}




Soft_fit<-function(Y, X, beta0, k=20, lam=1, rr=5, T=500, U=1, er=10^(-3), tag="N")
{

 # initializing------------------------------

  dX<-dim(X);  n<-dX[1]; p<-dX[2]
  X_t<-t(X);


   beta0 <- as.matrix(beta0, ncol=1)
   R_0 <- X %*% beta0

   if(tag=="B")
   { R_0<- exp(R_0) / (1+exp(R_0) ) }

   if(tag=="P")
   { R_0<- exp(R_0) }

    V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)

    tau_0 <- svd(X)$d[1]

   ############################
    uu<-  U/ tau_0^2
   ############################


# iteration start---------------------------

   u_c <- uu
   i<-1


repeat{

   repeat
      {
        gamma0<- beta0 + uu * V_0
        beta1<- Soft(t=gamma0, k=k, lam=lam)

        ########## u-check #################

         ucheck<- Uh(A=X, uh=uu, b0=beta0, b1=beta1, tag=tag)

         if( ucheck >= 1 )
         {break}else{ uu <- 0.5 * uu}

        ####################################

      }

      ######## convergence check ##############

        MSE<- sqrt(sum((beta1-beta0)^2))
        if( (i>1) && ((i>T) || (MSE < er)) ){break}

      #########################################

      beta0<-beta1
      ind_0<- (1:p)[beta0 != 0]

      bc_0<- beta0[ind_0]
      bc_0<-as.matrix(bc_0, ncol=1)
      Xs_0<-X[, ind_0]

      R_0<- Xs_0 %*% bc_0

      if(tag=="B")
      { R_0<- exp(R_0) / (1+exp(R_0) ) }

      if(tag=="P")
      { R_0<- exp(R_0) }

      V_0<-Fmt(A= X_t, a=Y - R_0, rr=rr)

      uu<-u_c
      i<-i+1

  }

 index<- (1:p)[beta1 != 0 ]

list(index=index, B=bc_0, step=i)
}




SCAD_EBIC<-function(Y, X, beta0, k.low, k.up, gg=0.5, pp=-1, rt=1, T=500, U=5, er=10^(-3), sig=1, tag="N")
{
  EBIC<- rep(0, k.up - k.low + 1)
  n<-length(Y)

  if(pp==-1)
  { pp<- dim(X)[2] }

  for(v in k.low:k.up)
  {
    ff<- SCAD_fit(Y=Y, X=X, beta0=beta0, k=v, er=er, T=T, U=U, rr=rt, tag=tag)
    X_s<-X[,ff$index]

    if(tag=="N")
    {
      ff_s <- lm(Y ~ X_s-1)
      bb_s <- as.vector(ff_s$coefficients)
     }

    if(tag=="B")
    {
      ff_s <- glm(Y ~ X_s-1, family=binomial)
      bb_s <- as.vector(ff_s$coefficients)
     }

    if(tag=="P")
    {
      ff_s <- glm(Y ~ X_s-1, family=poisson)
      bb_s <- as.vector(ff_s$coefficients)
     }

     ll<- lh(Y=Y, X=X_s, beta=bb_s, sig=sig, tag=tag)
     EBIC[v - k.low +1]<- -2 * ll + v * log(n) + 2 * v * gg * log(pp)

  }


    inx <- (1: (k.up - k.low + 1))[EBIC== min(EBIC)][1]

    v_s <- inx + k.low - 1
    f_s<- SCAD_fit(Y=Y, X=X, beta0=beta0, k=v_s, er=er, T=T, U=U, rr=rt, tag=tag)

   list(index=f_s$index, B=f_s$B, EBIC=EBIC )
}


Soft_EBIC<-function(Y, X, beta0, k.low, k.up, gg=0.5, pp=-1, rt=1, T=500, U=5, er=10^(-3), sig=1, tag="N")
{
  EBIC<- rep(0, k.up - k.low + 1)
  n<-length(Y)

  if(pp==-1)
  { pp<- dim(X)[2] }

  for(v in k.low:k.up)
  {
    ff<- Soft_fit(Y=Y, X=X, beta0=beta0, k=v, er=er, T=T, U=U, rr=rt, tag=tag)
    X_s<-X[,ff$index]

    if(tag=="N")
    {
      ff_s <- lm(Y ~ X_s-1)
      bb_s <- as.vector(ff_s$coefficients)
     }

    if(tag=="B")
    {
      ff_s <- glm(Y ~ X_s-1, family=binomial)
      bb_s <- as.vector(ff_s$coefficients)
     }

    if(tag=="P")
    {
      ff_s <- glm(Y ~ X_s-1, family=poisson)
      bb_s <- as.vector(ff_s$coefficients)
     }

     ll<- lh(Y=Y, X=X_s, beta=bb_s, sig=sig, tag=tag)
     EBIC[v - k.low +1]<- -2 * ll + v * log(n) + 2 * v * gg * log(pp)

  }


    inx <- (1: (k.up - k.low + 1))[EBIC== min(EBIC)][1]

    v_s <- inx + k.low - 1
    f_s<- Soft_fit(Y=Y, X=X, beta0=beta0, k=v_s, er=er, T=T, U=U, rr=rt, tag=tag)

   list(index=f_s$index, B=f_s$B, EBIC=EBIC )
}



SRT<-function(SR, MS, PR, PO, PPR=0, NPR=0, q)
{
  jj<-dim(SR)[1];  tt<-dim(SR)[2]

  PSR<-apply(SR, 1, mean) / q
  AMS<-apply(MS, 1, mean)
  FDR<-apply((MS - SR)/MS, 1, mean)

  SC<-SR
  SC[SC < q] <- 0; SC[SC==q]<- 1
  CP<-apply(SC, 1, mean)

  MC<-SC * MS
  MC[MC > q] <- 0; MC[MC==q]<-1
  CSR<- apply(MC, 1, mean)

  PE<-apply(PR, 1, mean)

  POO<-matrix(0, ncol=tt, nrow=jj)
  for(j in 1:jj)
  {POO[j,1:tt]<-PO}

  RPE<- 1 - apply( POO / PR, 1, mean )

 if(is.matrix(PPR))
  {PPR<- apply(PPR, 1, mean)
   NPR<- apply(NPR, 1, mean)
  }else{PPR<-0; NPR<-0}

  list(CP=CP, PSR=PSR, FDR=FDR, CSR=CSR, AMS=AMS, PPR=PPR, NPR=NPR,
       PE=PE, RPE=RPE, PO=mean(PO))

}


logit.pre<-function(Y, X, beta, cut=0.7)
{
   X<-as.matrix(X)
   beta<-as.matrix(beta, ncol=1)

   theta<-  X %*% beta
   mu<-  exp(theta)/(1 + exp(theta))

   pred<-rep(0, length(Y))
   pred[mu>=cut]<-1

   ppr<-cut; npr<- 1-cut

   if(length(Y[pred==1]) !=0)
   { ppr<- sum( Y[pred==1] ) / length(Y[pred==1])}

   if(length(Y[pred==0]) !=0)
   {npr<-  (length(Y[pred==0]) - sum( Y[pred==0] )) / length(Y[pred==0])}

   list(ppr=ppr, npr=npr)
}




