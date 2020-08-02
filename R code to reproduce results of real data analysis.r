rm(list=ls());gc()
wd = 'C:/Users/gz085/Downloads/OneDrive - Partners HealthCare/BWH/NLME censoring manuscript/'
setwd(wd)
library(nlme)
library(ggplot2)
library(data.table) 
library(mvtnorm)
library(quadprog)
tr <- function(A) {
  if (nrow(A) == 1) 
    a <- as.numeric(A)
  else a <- sum(diag(A))
  return(a)
}
bdiag <- function(x) {
  if (!is.list(x)) 
    stop("x not a list")
  n <- length(x)
  if (n == 0) 
    return(NULL)
  x <- lapply(x, function(y) if (length(y)) 
    as.matrix(y)
    else stop("Zero-length component in x"))
  d <- array(unlist(lapply(x, dim)), c(2, n))
  rr <- d[1, ]
  cc <- d[2, ]
  rsum <- sum(rr)
  csum <- sum(cc)
  out <- array(0, c(rsum, csum))
  ind <- array(0, c(4, n))
  rcum <- cumsum(rr)
  ccum <- cumsum(cc)
  ind[1, -1] <- rcum[-n]
  ind[2, ] <- rcum
  ind[3, -1] <- ccum[-n]
  ind[4, ] <- ccum
  imat <- array(1:(rsum * csum), c(rsum, csum))
  iuse <- apply(ind, 2, function(y, imat) imat[(y[1] + 
                                                  1):y[2], (y[3] + 1):y[4]], imat = imat)
  iuse <- as.vector(unlist(iuse))
  out[iuse] <- unlist(x)
  return(out)
} 
 
## modify the lmec function from the lmec package to fit LME model with censored responses and with beta subject to constraint t(Amat)* beta >=bvec  
lmec_Amat_bvec_constraint = function(yL, cens, X, Z, cluster, maxstep = 200,init,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000, Amat,bvec,meq=0)
{
  p <- ncol(X)
  q <- ncol(Z)
  m <- length(unique(cluster))
  n <- length(cluster)
  ni <- table(cluster)
  cl <- cluster
  lflag <- 0
  fit <- lm(yL ~ -1 + X) 
  if (missing(init) || is.na(match("beta", names(init)))) {
    
    beta <- fit$coef
    names(beta) <- NULL
  }
  else {
    beta <- init$beta
    names(beta) = NULL
  }
  if (missing(init) || is.na(match("sigma", names(init)))) 
  {  sigma2 <- (summary(fit)$sigma)^2 }
  else sigma2 <- init$sigma^2
  if (missing(init) || is.na(match("Delta", names(init)))) 
    Delta <- diag(rep(1, q))
  else Delta = init$Delta
  if (missing(init) || is.na(match("bi", names(init)))) 
    b <- matrix(rep(0, m * q), ncol = m)
  else b = init$bi
  
  old.lik <- 0
  likseq <- rep(0, maxstep)
  likseqex <- rep(0, maxstep)
  A <- matrix(nrow = n, ncol = p)
  # p is dim (fixed effects )
  a <- rep(0, n)
  # n = sum(ni); m = # of subjects
  #### QR decomposition to evaluate LME likelihood "Mixed-Effects Models in S and S-PLUS.pdf" Section 2.2 
  y = yL
  for (iter in (1:maxstep)) {
    lik <- s2 <- 0
    likex <- 0
    Psi <- Psi2 <- diag(0, q)
    for (i in 1:m) {
      Zi <- Z[cl == i, , drop = FALSE]
      # Zi design matrix for random effects
      Ziaug <- rbind(Zi, Delta)
      qrZ <- qr(Ziaug)
      Qi <- qr.Q(qrZ, compl = TRUE)[, , drop = FALSE]
      QTi <- qr.Q(qrZ, compl = TRUE)[1:ni[i], , drop = FALSE]
      QLTi <- QTi[, 1:q, drop = FALSE]
      QRTi <- QTi[, -(1:q), drop = FALSE]
      R11i <- qr.R(qrZ)
      R00i <- t(QRTi) %*% X[cl == i, , drop = FALSE]
      A[cl == i, ] <- R00i
      wi <- t(QLTi) %*% X[cl == i, , drop = FALSE] %*% 
        beta
      R11iinv <- solve(R11i)
      nic <- sum((cl == i) & (cens == 1))
      censi <- cens[cl == i]
      indi <- cbind(1:ni[i], censi)[, 1]
      
      if (nic == 0) {
        Ui <- diag(0, q)
        yo <- yL[(cl == i)]
        uo <- X[cl == i, , drop = FALSE] %*% beta
        invDelta <- solve(t(Delta) %*% Delta)
        So <- (sigma2 * (diag(1, ni[i]) + Zi %*% invDelta %*% 
                           t(Zi)))
      }
      if (nic > 0) {
        Xc <- X[cl == i & cens == 1, , drop = FALSE]
        Xo <- X[cl == i & cens == 0, , drop = FALSE]
        Zc <- Z[cl == i & cens == 1, , drop = FALSE]
        Zo <- Z[cl == i & cens == 0, , drop = FALSE]
        qc <- yL[(cl == i) & cens == 1]
        yo <- yL[(cl == i) & cens == 0]
        indc <- indi[censi == 1]
        indo <- indi[censi == 0]
        QLic <- Qi[-indo, 1:q, drop = FALSE]
        QLio <- Qi[-indc, 1:q, drop = FALSE]
        QLTic <- QLTi[indc, , drop = FALSE]
        QLTio <- QLTi[indo, , drop = FALSE]
        invQLio2 <- solve(t(QLio) %*% QLio)
        u <- Xc %*% beta + {
          QLTic %*% invQLio2 %*% t(QLTio)
        } %*% (yo - Xo %*% beta)
        S <- sigma2 * {
          diag(1, nic) + QLTic %*% invQLio2 %*% t(QLTic)
        }
        uo <- Xo %*% beta
        invDelta <- solve(t(Delta) %*% Delta)
        So <- (sigma2 * (diag(1, ni[i]) + Zi %*% invDelta %*% 
                           t(Zi)))[indo, indo]
        if (nic == 1) {
          qq <- (1/sqrt(S)) * (-qc + u)
          R <- 1
          alpha <- pnorm(-qq)
          dd <- dnorm(-qq)
          H <- qq * dd
          EX <- (1/alpha) * dd
          EXX <- 1 + 1/alpha * H
          varX <- EXX - EX^2
          Eycens <- -sqrt(S) * EX + u
          varyic <- varX * S
        }
        else {
          qq <- diag(1/sqrt(diag(S))) %*% (-qc + u)
          R <- diag(1/sqrt(diag(S))) %*% S %*% diag(1/sqrt(diag(S)))
          alpha <- pmvnorm(upper = as.vector(-qq), 
                           corr = R, abseps = abspmv)
          dd <- rep(0, nic)
          for (j in 1:nic) {
            V <- R[-j, -j, drop = FALSE] - R[-j, j, 
                                             drop = FALSE] %*% R[j, -j, drop = FALSE]
            nu <- -qq[-j] + R[-j, j, drop = FALSE] %*% 
              qq[j]
            dd[j] <- dnorm(-qq[j]) * pmvnorm(upper = as.vector(nu), 
                                             sigma = V, abseps = abspmv)
          }
          H <- matrix(rep(0, nic * nic), nrow = nic)
          RH <- matrix(rep(0, nic * nic), nrow = nic)
          if (nic == 2) {
            H[1, 2] <- H[2, 1] <- dmvnorm(-qq[c(1, 
                                                2)], sigma = matrix(c(1, R[1, 2], R[2, 
                                                                                    1], 1), nrow = 2))
            RH[1, 2] <- RH[2, 1] <- R[1, 2] * H[1, 
                                                2]
          }
          else {
            for (s in 1:(nic - 1)) {
              for (t in (s + 1):nic) {
                invR <- solve(R[c(s, t), c(s, t), drop = FALSE])
                nu <- -qq[-c(s, t)] + R[-c(s, t), c(s, 
                                                    t), drop = FALSE] %*% invR %*% qq[c(s, 
                                                                                        t), , drop = FALSE]
                V <- R[-c(s, t), -c(s, t), drop = FALSE] - 
                  R[-c(s, t), c(s, t), drop = FALSE] %*% 
                  invR %*% R[c(s, t), -c(s, t), drop = FALSE]
                H[s, t] <- H[t, s] <- pmvnorm(upper = as.vector(nu), 
                                              sigma = V, abseps = abspmv) * dmvnorm(-qq[c(s, 
                                                                                          t)], sigma = matrix(c(1, R[s, t], 
                                                                                                                R[t, s], 1), nrow = 2))
                RH[s, t] <- RH[t, s] <- R[s, t] * H[s, 
                                                    t]
              }
            }
          }
          h <- qq * dd - apply(RH, 1, sum)
          diag(H) <- h
          EX <- (1/alpha) * R %*% dd
          EXX <- R + 1/alpha * R %*% H %*% R
          varX <- EXX - EX %*% t(EX)
          Eycens <- -diag(sqrt(diag(S))) %*% EX + u
          varyic <- diag(sqrt(diag(S))) %*% varX %*% 
            diag(sqrt(diag(S)))
        }
        trvaryic <- tr(varyic)
        Ui <- t(QLTic) %*% varyic %*% QLTic
        s2 <- s2 + trvaryic/n - tr(Ui)/n
        y[(cl == i) & (cens == 1)] <- Eycens
      }
      c0i <- t(QRTi) %*% y[cl == i]
      a[cl == i] <- c0i[, 1]
      c1i <- t(QLTi) %*% y[cl == i]
      bi = R11iinv %*% (c1i - wi)
      b[, i] <- bi
      Wi = R11iinv %*% t(R11iinv)
      Psi <- Psi + 1/m * R11iinv %*% ((c1i - wi) %*% 
                                        t(c1i - wi) + Ui) %*% t(R11iinv)
      Psi2 <- Psi2 + 1/m * Wi
      lik <- lik - sum(log(abs(diag(R11i))))
      if (nic == 0) 
        likex <- likex + log(dmvnorm(yo, mean = as.vector(uo), 
                                     sigma = So))
      else {
        if (nic == ni[i]) 
          likex <- likex + log(alpha)
        else {
          if (ni[i] - nic == 1) 
            likex <- likex + log(alpha) + log(dnorm(yo, 
                                                    mean = uo, sd = sqrt(So)))
          else likex <- likex + log(alpha) + log(dmvnorm(yo, 
                                                         mean = as.vector(uo), sigma = So))
        }
      }
      if (iter > 10) {
        QRTic <- QRTi[cens[cl == i] == 1, , drop = FALSE]
        if (nic == 0) 
          Vi <- diag(ni[i]) - diag(ni[i])
        else Vi <- t(QRTic) %*% varyic %*% QRTic
        if (i == 1) {
          inv.varbeta1 = t(R00i) %*% R00i
          inv.varbeta2 = t(R00i) %*% Vi %*% R00i
        }
        else {
          inv.varbeta1 = inv.varbeta1 + t(R00i) %*% 
            R00i
          inv.varbeta2 = inv.varbeta2 + t(R00i) %*% 
            Vi %*% R00i
        }
      }
    }
    qra <- qr(A)
    cc = t(qr.Q(qra, compl = TRUE)) %*% a
    
    Rmat = qr.R(qra)
    c1vec =  cc[1:p, 1]
    
    # beta <- solve(Rmat, c1vec) # unconstrained beta = arg min (Rmat beta - c1vec)^T (Rmat beta - c1vec) 
    
    #### # solving quadratic programming problems of the form min(-d^T b + 1/2b^T D b) with the constraints A^T b >= b0 
    Dmat = 2*t(Rmat)%*%Rmat
    dvec = as.numeric(2*t(Rmat)%*%c1vec)
    out = solve.QP(Dmat, dvec, Amat=Amat, bvec=bvec, meq=meq, factorized=FALSE)
    beta = out$solution
    
    sigma2 <- s2 + sum(cc[(p + 1):n]^2)/n
    if (!is.matrix(Delta)) 
      Delta <- matrix(Delta)
    lik <- lik - n/2 * (1 + log(2 * pi)) - n/2 * log(sigma2) + 
      m * sum(log(diag(Delta)))
    Psi <- Psi + Psi2 * sigma2
    
    Delta <- chol(solve(Psi/sigma2))
    likseq[iter] <- lik
    likseqex[iter] <- likex
    diff <- likseqex[iter] - likseqex[iter - 1]
    if (iter > 10 && diff < epsstop) 
      if (lflag == 0) 
        lflag <- 1
    else lflag <- 2
    # print(paste(c(iter, lflag, diff, likex), sep = " "))
    if (iter == maxstep | lflag == 2) {
      varFix = sigma2 * solve(inv.varbeta1 - inv.varbeta2/sigma2)
      break
    }
    
  }
  return(list(beta = beta, bi = b, sigma = sqrt(sigma2), 
              Psi = Psi, Delta = Delta, loglik = lik, loglikex = likex, 
              varFix = varFix, 
              step = iter, likseq = likseq[1:iter], likseqex = likseqex[1:iter]))
}

############ 
# ACTG 315 data example  
############
set.seed(1)
dat = read.table('dt315.txt',header = TRUE,skip=2)
# dt315.txt is orginally downloaded from Prof. Hulin Wu's AIDS data webpage 
dat = dat[dat$Day<95,]# only consider first 3 month data (short-term viral dynamics as in Wang and Wu 2013)
names(dat) = c("obs","id","day","lgcopy","cd4")
dat$day_rescal = dat$day/max(dat$day) # scale(dat_combined_observed_cd4$day)
dat$cd4_rescal = scale(dat$cd4)
summary(dat$lgcopy) # 1.69=log10(100/2) represents censored responses
dat$cens = ifelse(dat$lgcopy<1.999,1,0)
mean(dat$cens) 
dat = as.data.table(dat)
dat[,.N,by=id]
range(dat[,.N,by=id][,N])
p2 = ggplot(data = dat, aes(x = day, y = lgcopy))+geom_line(aes(group = id),alpha=0.3)+geom_point(alpha=0.6,aes(color=as.factor(cens),shape=as.factor(cens)))+scale_color_manual(values=c('black','red'))+scale_shape_manual(values=c(1,19))+theme_classic()+labs(x='Day',y='Viral load (log10-scale)',title='Viral Load with Censoring in the ACTG 315 study') +geom_hline(yintercept = 2,linetype='dotted')+ annotate("text",label="Detection limit",x =12, y =1.916,size=3.64,hjust=1)+scale_y_continuous(limits = c(1,7),breaks=1:7)+ theme(plot.title = element_text(hjust = 0.5),legend.position = 'none')
p2
ggsave(file="figure1.pdf", p2,width = 6,height = 5)

r1 = table(dat$id)
sum(r1>5)
biexp315 <- deriv( ~ log(exp(beta1-beta2*x1-beta3*x2*x1) + exp(beta4-beta5*x1))/log(10),    c("beta1","beta2","beta3","beta4","beta5"), function(x1,x2,beta1,beta2,beta3,beta4,beta5){})

full_iteration = 1
for(full_iteration in 1:100)
{ 
  if(full_iteration==1) 
  { 
    nls_for_initial = nls(lgcopy~log10(exp(p1-lamb1*day_rescal-a1*cd4_rescal*day_rescal)+exp(p2-lamb2*day_rescal)),data=dat,start=list(p1=10,lamb1=20,a1=0,p2=7,lamb2=1))
    summary(nls_for_initial) 
    start2 = summary(nls_for_initial)$coef[,1]
    
    dat = groupedData(lgcopy~day_rescal|id,data=dat)
    fm1 =  nlme(lgcopy ~ log10(exp(p1-lamb1*day_rescal-a1*cd4_rescal*day_rescal) + exp(p2-lamb2*day_rescal)),  data = dat,  fixed = p1 + lamb1 + a1 + p2 + lamb2 ~ 1, random = p1+lamb1+p2+lamb2~1,   start = list(fixed=start2),verbose=TRUE,control=nlmeControl(maxIter=1, pnlsMaxIter=2000, msMaxIter=500, minScale=1e-7,  tolerance=3e-2, niterEM=1000, pnlsTol=5e-3, msTol=1e-7, returnObject=TRUE, msVerbose=FALSE))
    summary(fm1)
    m = length(unique(dat$id) )
    bi_estimate=as.data.table(fm1$coefficients$random$id)
    bi_estimate[,id:=as.numeric(rownames(fm1$coefficients$random$id))]
    bi_estimate = bi_estimate[order(id)]
    beta_old = fm1$coefficients$fixed
    b_old = matrix(rep(0, 4*m), ncol=m); 
    for(k in 1:m) b_old[,k] = as.numeric(bi_estimate[k,1:4])
  }
  
  y=dat$lgcopy; cens=dat$cens; cluster=as.numeric(as.character(dat$id));  x=as.matrix(as.data.frame(dat)[,c('day_rescal','cd4_rescal')]); fun=biexp315; epsilon=1e-3; bi.subset = c(1,2,4,5);  sigma2=0.5;   method="ML"; varstruct="unstructured";  maxstep=2000; verbose=T; epsstop=1e-3 
  beta = beta_old; 
  b = b_old
  r = dim(x)[2]
  m = length(unique(cluster))
  n = length(cluster)
  ni = table(cluster)
  cl = cluster
  p = length(beta)
  q = ifelse(all(bi.subset==0), p, length(bi.subset))
  X = matrix(rep(0,n*p), ncol=p)
  Z = matrix(rep(0,n*q), ncol=q)
  yl = rep(NA,length(y))
  ###### Linearization step
  for (i in 1:m)
  {  
    betai = beta; 
    betai[bi.subset] = betai[bi.subset] + b[,i]
    fx.arg = as.list(c(x[1,], betai))
    for(j in 1:r) fx.arg[[j]] = x[cluster==i,j]
    names(fx.arg) = c(paste("x",1:r,sep=""),paste("beta",1:p,sep=""))
    formals(fun) = fx.arg
    fx = fun()
    X[cluster==i,] = Xi = attr(fx,"gradient")
    Z[cluster==i,] = Zi = Xi[, bi.subset,drop=F]
    yl[cluster==i] = y[cluster==i] - as.numeric(fx) + Xi %*% beta + Zi %*% b[,i]
  }  
  ###### LME step (with order constraints incorporated)
  lme_out315 = lmec_Amat_bvec_constraint(yL=yl, cens=cens, X=X, Z=Z, cluster=cluster,init=list(beta=beta,b), maxstep = 200,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000, Amat=t(rbind(c(0,1,0,0,0),c(0,0,0,0,1))),bvec=c(0,0),meq=0)
  beta_new = lme_out315$beta
  absolute_beta_old_new = abs(beta_old - beta_new)
  relative_beta_old_new = abs(beta_old - beta_new)/abs(beta_old)
  beta_old = beta_new
  b_old = lme_out315$bi
  cat(paste0('full_iteration=',full_iteration,'; max(abs_beta)=',max(absolute_beta_old_new),'; max(rel_beta)=',max(relative_beta_old_new),'\n'))
  if(max(relative_beta_old_new)<0.0005) break;
}
beta_est = lme_out315$beta 
cov_beta_est = lme_out315$varFix
sd_beta_est = sqrt(diag(cov_beta_est))
t_ratio_beta = beta_est/sd_beta_est;

#two-sided univariate pvalues 
round(2*pnorm(t_ratio_beta,lower.tail = FALSE),3)
#one-sided univariate pvalues
round(pnorm(t_ratio_beta,lower.tail = FALSE),3)
 
# estimation under H0
full_iteration = 1
for(full_iteration in 1:100)
{ 
  if(full_iteration==1) 
  { 
    nls_for_initial = nls(lgcopy~log10(exp(p1-lamb1*day_rescal-a1*cd4_rescal*day_rescal)+exp(p2-lamb2*day_rescal)),data=dat,start=list(p1=10,lamb1=20,a1=0,p2=7,lamb2=1))
    summary(nls_for_initial) 
    start2 = summary(nls_for_initial)$coef[,1]
    
    dat = groupedData(lgcopy~day_rescal|id,data=dat)
    fm1 =  nlme(lgcopy ~ log10(exp(p1-lamb1*day_rescal-a1*cd4_rescal*day_rescal) + exp(p2-lamb2*day_rescal)),  data = dat,  fixed = p1 + lamb1 + a1 + p2 + lamb2 ~ 1, random = p1+lamb1+p2+lamb2~1,   start = list(fixed=start2),verbose=TRUE,control=nlmeControl(maxIter=1, pnlsMaxIter=2000, msMaxIter=500, minScale=1e-7,  tolerance=1, niterEM=1000, pnlsTol=5e-3, msTol=1e-7, returnObject=TRUE, msVerbose=FALSE))
    summary(fm1)
    m = length(unique(dat$id) )
    bi_estimate=as.data.table(fm1$coefficients$random$id)
    bi_estimate[,id:=as.numeric(rownames(fm1$coefficients$random$id))]
    bi_estimate = bi_estimate[order(id)]
    
    beta_old = fm1$coefficients$fixed
    b_old = matrix(rep(0, 4*m), ncol=m); 
    for(k in 1:m) b_old[,k] = as.numeric(bi_estimate[k,1:4])
  }
  y=dat$lgcopy; cens=dat$cens; cluster=as.numeric(as.character(dat$id));  x=as.matrix(as.data.frame(dat)[,c('day_rescal','cd4_rescal')]); fun=biexp315; epsilon=1e-3; bi.subset = c(1,2,4,5);  sigma2=0.5;   method="ML"; varstruct="unstructured";  maxstep=2000; verbose=T; epsstop=1e-3 
  beta = beta_old; 
  b = b_old
  r = dim(x)[2]
  m = length(unique(cluster))
  n = length(cluster)
  ni = table(cluster)
  cl = cluster
  p = length(beta)
  q = ifelse(all(bi.subset==0), p, length(bi.subset))
  X = matrix(rep(0,n*p), ncol=p)
  Z = matrix(rep(0,n*q), ncol=q)
  yl = rep(NA,length(y))
  ###### Linearization step
  for (i in 1:m)
  {  
    betai = beta; 
    betai[bi.subset] = betai[bi.subset] + b[,i]
    fx.arg = as.list(c(x[1,], betai))
    for(j in 1:r) fx.arg[[j]] = x[cluster==i,j]
    names(fx.arg) = c(paste("x",1:r,sep=""),paste("beta",1:p,sep=""))
    formals(fun) = fx.arg
    fx = fun()
    X[cluster==i,] = Xi = attr(fx,"gradient")
    Z[cluster==i,] = Zi = Xi[, bi.subset,drop=F]
    yl[cluster==i] = y[cluster==i] - as.numeric(fx) + Xi %*% beta + Zi %*% b[,i]
  }  
  ###### LME step (with order constraints incorporated)
  lme_out315H0 = lmec_Amat_bvec_constraint(yL=yl, cens=cens, X=X, Z=Z, cluster=cluster,init=list(beta=beta,b), maxstep = 200,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000, Amat=t(rbind(c(0,1,0,0,0),c(0,0,0,0,1))),bvec=c(0,0),meq=2) # meq=2 indicates lamb1 and lamb2 are forced to be 0 (consistent with H0)
  beta_new = lme_out315H0$beta
  loglike_new = lme_out315H0$likseq[length(lme_out315H0$likseq)]
  
 
  beta_old = beta_new
  b_old = lme_out315H0$bi
  if(full_iteration>1) { 
  rel_loglike = abs(loglike_new-loglike_old)/abs(loglike_old)
  cat(paste0('full_iteration=',full_iteration,'; max(rel_loglike)=',max(rel_loglike),'\n'))
  if(max(rel_loglike)<0.06) break;
  }
  loglike_old = loglike_new
}

lamb_vec = c(lme_out315$beta[2],lme_out315$beta[5])
cov_lamb_vec = lme_out315$varFix[c(2,5),c(2,5)]
inv_cov_lamb_vec = solve(cov_lamb_vec)
Tw315 = (t(lamb_vec)%*%inv_cov_lamb_vec%*%lamb_vec)[1,1]
q =  acos(cov_lamb_vec[1,2]/sqrt(cov_lamb_vec[1,1]*cov_lamb_vec[2,2]) )/(2*pi);
Tw_pval315 = 1-q-0.5*pchisq(Tw315,df=1)-(0.5-q)*pchisq(Tw315,df=2) 
Tw_pval315
Tlr315 =  2*(lme_out315$likseq[length(lme_out315$likseq)]-lme_out315H0$likseq[length(lme_out315H0$likseq)])
Tlr_pval315 = 1-q-0.5*pchisq(Tlr315,df=1)-(0.5-q)*pchisq(Tlr315,df=2) 
Tlr_pval315

## naive method (half detection limit imputation)
full_iteration = 1
for(full_iteration in 1:100)
{ 
  if(full_iteration==1) 
  { 
    nls_for_initial = nls(lgcopy~log10(exp(p1-lamb1*day_rescal-a1*cd4_rescal*day_rescal)+exp(p2-lamb2*day_rescal)),data=dat,start=list(p1=10,lamb1=20,a1=0,p2=7,lamb2=1))
    summary(nls_for_initial) 
    start2 = summary(nls_for_initial)$coef[,1]
    
    dat = groupedData(lgcopy~day_rescal|id,data=dat)
    fm1 =  nlme(lgcopy ~ log10(exp(p1-lamb1*day_rescal-a1*cd4_rescal*day_rescal) + exp(p2-lamb2*day_rescal)),  data = dat,  fixed = p1 + lamb1 + a1 + p2 + lamb2 ~ 1, random = p1+lamb1+p2+lamb2~1,   start = list(fixed=start2),verbose=TRUE,control=nlmeControl(maxIter=1, pnlsMaxIter=2000, msMaxIter=500, minScale=1e-7,  tolerance=3e-2, niterEM=1000, pnlsTol=5e-3, msTol=1e-7, returnObject=TRUE, msVerbose=FALSE))
    summary(fm1)
    m = length(unique(dat$id) )
    bi_estimate=as.data.table(fm1$coefficients$random$id)
    bi_estimate[,id:=as.numeric(rownames(fm1$coefficients$random$id))]
    bi_estimate = bi_estimate[order(id)]
    
    beta_old = fm1$coefficients$fixed
    b_old = matrix(rep(0, 4*m), ncol=m);
    for(k in 1:m) b_old[,k] = as.numeric(bi_estimate[k,1:4])
  }
  y=dat$lgcopy; cens=rep(0,length(y)); cluster=as.numeric(as.character(dat$id));  x=as.matrix(as.data.frame(dat)[,c('day_rescal','cd4_rescal')]); fun=biexp315; epsilon=1e-3; bi.subset = c(1,2,4,5);  sigma2=0.5;   method="ML"; varstruct="unstructured";  maxstep=2000; verbose=T; epsstop=1e-3 
  beta = beta_old; 
  b = b_old
  r = dim(x)[2]
  m = length(unique(cluster))
  n = length(cluster)
  ni = table(cluster)
  cl = cluster
  p = length(beta)
  q = ifelse(all(bi.subset==0), p, length(bi.subset))
  X = matrix(rep(0,n*p), ncol=p)
  Z = matrix(rep(0,n*q), ncol=q)
  yl = rep(NA,length(y))
  ###### Linearization step
  for (i in 1:m)
  {  
    betai = beta; 
    betai[bi.subset] = betai[bi.subset] + b[,i]
    fx.arg = as.list(c(x[1,], betai))
    for(j in 1:r) fx.arg[[j]] = x[cluster==i,j]
    names(fx.arg) = c(paste("x",1:r,sep=""),paste("beta",1:p,sep=""))
    formals(fun) = fx.arg
    fx = fun()
    X[cluster==i,] = Xi = attr(fx,"gradient")
    Z[cluster==i,] = Zi = Xi[, bi.subset,drop=F]
    yl[cluster==i] = y[cluster==i] - as.numeric(fx) + Xi %*% beta + Zi %*% b[,i]
  }  
  ###### LME step (with order constraints incorporated)
  lme_out315_naive = lmec_Amat_bvec_constraint(yL=yl, cens=cens, X=X, Z=Z, cluster=cluster,init=list(beta=beta,b), maxstep = 200,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000,  Amat=t(rbind(c(0,1,0,0,0),c(0,0,0,0,1))),bvec=c(0,0),meq=0)
  beta_new = lme_out315_naive$beta
  absolute_beta_old_new = abs(beta_old - beta_new)
  relative_beta_old_new = abs(beta_old - beta_new)/abs(beta_old)
  beta_old = beta_new
  b_old = lme_out315_naive$bi
  cat(paste0('full_iteration=',full_iteration,'; max(abs_beta)=',max(absolute_beta_old_new),'; max(rel_beta)=',max(relative_beta_old_new),'\n'))
  if(max(relative_beta_old_new)<0.0006) break;
}
save(lme_out315,lme_out315_naive,Tw315,Tlr315,Tw_pval315,Tlr_pval315,file='315results')

####  Figure 3
P1 = lme_out315$beta[1]
lamb1 = lme_out315$beta[2]
alpha = lme_out315$beta[3]
P2 = lme_out315$beta[4]
lamb2 = lme_out315$beta[5]
pdf("Figure 3.pdf",width=6,height=6)
unique_pat_id = unique(dat$id)
total_sub = length(unique_pat_id)
par(mar=c(3.9,3.9,2.2,0.5))
ran_sub_id_index =  c(4,14,27,39) 
dat = as.data.frame(dat)
par(mfrow=c(2,2))
for(k in 1:length(ran_sub_id_index))
{
  dt = dat[dat$id==unique_pat_id[ran_sub_id_index[k]],]
  # print(dt[,c("logrna_NA_imputed","patid","day_rescal")])
  plot(dt$lgcopy~dt$day_rescal,type="n",xlab="Re-scaled time",ylab="log10 viral load",ylim=c(0.5,7.1),xlim=c(0,1),main=paste("Subject ",ran_sub_id_index[k],sep = " "),mgp=c(2.1,1,0))
  points(dt$day_rescal[dt$cens<0.5],dt$lgcopy[dt$cens<0.5],cex=2,pch=16) # uncensored
  points(dt$day_rescal[dt$cens>0.5],dt$lgcopy[dt$cens>0.5],pch=16,cex=1,col="red")  #censored 
  abline(h=2,lty=3,lwd=2)
  bi1 = lme_out315$bi[1,ran_sub_id_index[k]]
  bi2 = lme_out315$bi[2,ran_sub_id_index[k]] 
  bi3 = lme_out315$bi[3,ran_sub_id_index[k]]
  bi4 = lme_out315$bi[4,ran_sub_id_index[k]]
  curve(log10( exp(P1 + bi1 -lamb1*x - bi2*x-alpha*as.numeric(dt[,'cd4_rescal'])*x) + exp(P2+bi3-lamb2*x - bi4*x)),from=min(dt$day_rescal,na.rm=TRUE),to=max(dt$day_rescal,na.rm=TRUE),lty=1,add = TRUE)
}
par(mfrow=c(1,1))
dev.off()




############ 
# ACTG 398 data example  
############
set.seed(1)
a398 = read.table("398raw.txt",header = TRUE,sep="")
# 398raw.txt is orginally downloaded from Prof. Hulin Wu's AIDS data webpage 
a398 = as.data.table(a398)
a398[,list(N=length(unique(patid))),by=trtarm] 
# arm 2 with 69 subjects is indinavir, https://jamanetwork.com/journals/jama/fullarticle/195095
a398_2 = a398[trtarm==2 &cens<1.5]
a398_2[,day_rescal:=txday/max(txday)]
r1 = tapply(a398_2$patid,a398_2$patid,length)
r1
range(a398_2$txday)
mean(a398_2$cens) #   censoring rate
biexp <- deriv( ~ log(exp(beta1-beta2*x1) + exp(beta3-beta4*x1))/log(10), 
                c("beta1","beta2","beta3","beta4"), function(x1,beta1,beta2,beta3,beta4){})

full_iteration = 1
for(full_iteration in 1:100)
{ 
  if(full_iteration==1) 
  { 
    nls_for_initial   = nls(logrna~log10(exp(p1-lamb1*day_rescal)+exp(p2-lamb2*day_rescal)),data=a398_2,start=list(p1=10,lamb1=68,p2=7,lamb2=1)) 
    start2 = summary(nls_for_initial)$coef[,1]
    
    a398_2$id=as.numeric(as.character(a398_2$patid))
    dat = groupedData(logrna~1|id,data=a398_2)
    
    fm1 =  nlme(logrna~log10(exp(P1-lamb1*day_rescal)+exp(P2-lamb2*day_rescal)),  data = dat,  fixed = P1+lamb1+P2+lamb2 ~ 1, random = P1+lamb1+P2+lamb2~1,   start =start2,verbose=TRUE,control=nlmeControl(maxIter=1, pnlsMaxIter=2000, msMaxIter=500, minScale=1e-7,  tolerance=0.98, niterEM=1000, pnlsTol=5e-3, msTol=1e-7, returnObject=TRUE, msVerbose=FALSE))
    summary(fm1)
    
    m = length(unique(dat$id) )
    bi_estimate=as.data.table(fm1$coefficients$random$id)
    bi_estimate[,id:=as.numeric(rownames(fm1$coefficients$random$id))]
    bi_estimate = bi_estimate[order(id)]
    beta_old = fm1$coefficients$fixed
    b_old = matrix(rep(0, 4*m), ncol=m); 
    for(k in 1:m) b_old[,k] = as.numeric(bi_estimate[k,1:4])
  }
  
  
  cluster_dt = as.data.table(dat)[,.N,by=id][order(as.numeric(as.character(id)))]; cluster_dt[,cluster:=1:nrow(cluster_dt)] 
  dat2=merge(as.data.table(dat),cluster_dt[,.(id,cluster)],by.x='id',by.y='id')[order(cluster)]
  y=dat$logrna; cens=dat$cens; cluster=dat2[,cluster];  x=as.matrix(as.data.frame(dat)[,c('day_rescal')]); fun=biexp; epsilon=1e-3; bi.subset = c(1,2,3,4);  sigma2=0.5;   method="ML"; varstruct="unstructured";  maxstep=2000; verbose=T; epsstop=1e-3 
  beta = beta_old; 
  b = b_old
  r = dim(x)[2]
  m = length(unique(cluster))
  n = length(cluster)
  ni = table(cluster)
  cl = cluster
  p = length(beta)
  q = ifelse(all(bi.subset==0), p, length(bi.subset))
  X = matrix(rep(0,n*p), ncol=p)
  Z = matrix(rep(0,n*q), ncol=q)
  yl = rep(NA,length(y))
  ###### Linearization step
  for (i in 1:m)
  {  
    betai = beta; 
    betai[bi.subset] = betai[bi.subset] + b[,i]
    fx.arg = as.list(c(x[1,], betai))
    for(j in 1:r) fx.arg[[j]] = x[cluster==i,j]
    names(fx.arg) = c(paste("x",1:r,sep=""),paste("beta",1:p,sep=""))
    formals(fun) = fx.arg
    fx = fun()
    X[cluster==i,] = Xi = attr(fx,"gradient")
    Z[cluster==i,] = Zi = Xi[, bi.subset,drop=F]
    yl[cluster==i] = y[cluster==i] - as.numeric(fx) + Xi %*% beta + Zi %*% b[,i]
  }  
  ###### LME step (with order constraints incorporated)
  lme_out398 = lmec_Amat_bvec_constraint(yL=yl, cens=cens, X=X, Z=Z, cluster=cluster,init=list(beta=beta,b), maxstep = 200,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000, Amat=t(rbind(c(0,1,0,0),c(0,0,0,1))),bvec=c(0,0))
  beta_new = lme_out398$beta
  absolute_beta_old_new = abs(beta_old - beta_new)
  relative_beta_old_new = abs(beta_old - beta_new)/abs(beta_old)
  beta_old = beta_new
  b_old = lme_out398$bi
  cat(paste0('full_iteration=',full_iteration,'; max(abs_beta)=',max(absolute_beta_old_new),'; max(rel_beta)=',max(relative_beta_old_new),'\n'))
  if(max(relative_beta_old_new)<0.001) break;
}

beta_est = lme_out398$beta 
cov_beta_est = lme_out398$varFix
sd_beta_est = sqrt(diag(cov_beta_est))
t_ratio_beta = beta_est/sd_beta_est; beta_est;sd_beta_est ; t_ratio_beta
#two-sided univariate pvalues 
round(2*pnorm(t_ratio_beta,lower.tail = FALSE),3)
#one-sided univariate pvalues
round(pnorm(t_ratio_beta,lower.tail = FALSE),3)

# estimation under H0
full_iteration = 1
for(full_iteration in 1:100)
{ 
  if(full_iteration==1) 
  { 
    nls_for_initial   = nls(logrna~log10(exp(p1-lamb1*day_rescal)+exp(p2-lamb2*day_rescal)),data=a398_2,start=list(p1=10,lamb1=68,p2=7,lamb2=1)) 
    start2 = summary(nls_for_initial)$coef[,1]
    
    a398_2$id=as.numeric(as.character(a398_2$patid))
    dat = groupedData(logrna~1|id,data=a398_2)
    
    fm1 =  nlme(logrna~log10(exp(P1-lamb1*day_rescal)+exp(P2-lamb2*day_rescal)),  data = dat,  fixed = P1+lamb1+P2+lamb2 ~ 1, random = P1+lamb1+P2+lamb2~1,   start =start2,verbose=TRUE,control=nlmeControl(maxIter=1, pnlsMaxIter=2000, msMaxIter=500, minScale=1e-7,  tolerance=0.98, niterEM=1000, pnlsTol=5e-3, msTol=1e-7, returnObject=TRUE, msVerbose=FALSE))
    summary(fm1)
    
    m = length(unique(dat$id) )
    bi_estimate=as.data.table(fm1$coefficients$random$id)
    bi_estimate[,id:=as.numeric(rownames(fm1$coefficients$random$id))]
    bi_estimate = bi_estimate[order(id)]
    beta_old = fm1$coefficients$fixed
    b_old = matrix(rep(0, 4*m), ncol=m); 
    for(k in 1:m) b_old[,k] = as.numeric(bi_estimate[k,1:4])
  }
  
  
  cluster_dt = as.data.table(dat)[,.N,by=id][order(as.numeric(as.character(id)))]; cluster_dt[,cluster:=1:nrow(cluster_dt)] 
  dat2=merge(as.data.table(dat),cluster_dt[,.(id,cluster)],by.x='id',by.y='id')[order(cluster)]
  y=dat$logrna; cens=dat$cens; cluster=dat2[,cluster];  x=as.matrix(as.data.frame(dat)[,c('day_rescal')]); fun=biexp; epsilon=1e-3; bi.subset = c(1,2,3,4);  sigma2=0.5;   method="ML"; varstruct="unstructured";  maxstep=2000; verbose=T; epsstop=1e-3 
  beta = beta_old; 
  b = b_old
  r = dim(x)[2]
  m = length(unique(cluster))
  n = length(cluster)
  ni = table(cluster)
  cl = cluster
  p = length(beta)
  q = ifelse(all(bi.subset==0), p, length(bi.subset))
  X = matrix(rep(0,n*p), ncol=p)
  Z = matrix(rep(0,n*q), ncol=q)
  yl = rep(NA,length(y))
  ###### Linearization step
  for (i in 1:m)
  {  
    betai = beta; 
    betai[bi.subset] = betai[bi.subset] + b[,i]
    fx.arg = as.list(c(x[1,], betai))
    for(j in 1:r) fx.arg[[j]] = x[cluster==i,j]
    names(fx.arg) = c(paste("x",1:r,sep=""),paste("beta",1:p,sep=""))
    formals(fun) = fx.arg
    fx = fun()
    X[cluster==i,] = Xi = attr(fx,"gradient")
    Z[cluster==i,] = Zi = Xi[, bi.subset,drop=F]
    yl[cluster==i] = y[cluster==i] - as.numeric(fx) + Xi %*% beta + Zi %*% b[,i]
  }  
  ###### LME step (with order constraints incorporated)
  lme_out398H0 = lmec_Amat_bvec_constraint(yL=yl, cens=cens, X=X, Z=Z, cluster=cluster,init=list(beta=beta,b), maxstep = 200,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000, Amat=t(rbind(c(0,1,0,0),c(0,0,0,1))),bvec=c(0,0),meq=2)
  beta_new = lme_out398H0$beta
  beta_old = beta_new
  b_new = lme_out398H0$bi
  b_old = b_new
  
  loglike_new = lme_out398H0$likseq[length(lme_out398H0$likseq)]
  if(full_iteration>1) { 
    rel_loglike = abs(loglike_new-loglike_old)/abs(loglike_old)
    cat(paste0('full_iteration=',full_iteration,'; max(rel_loglike)=',max(rel_loglike),'\n'))
    if(max(rel_loglike)<0.06) break;
  }
  loglike_old = loglike_new
}


# multivariate test of lamb1=lamb2=0
lamb_vec = c(lme_out398$beta[2],lme_out398$beta[4])
cov_lamb_vec = lme_out398$varFix[c(2,4),c(2,4)]
inv_cov_lamb_vec = solve(cov_lamb_vec)
Tw398 = (t(lamb_vec)%*%inv_cov_lamb_vec%*%lamb_vec)[1,1]
q =  acos(cov_lamb_vec[1,2]/sqrt(cov_lamb_vec[1,1]*cov_lamb_vec[2,2]) )/(2*pi);
Tw_pval398 = 1-q-0.5*pchisq(Tw398,df=1)-(0.5-q)*pchisq(Tw398,df=2) 
Tw_pval398
Tlr398 =  2*(lme_out398$likseq[length(lme_out398$likseq)]-lme_out398H0$likseq[length(lme_out398H0$likseq)])
Tlr_pval398 = 1-q-0.5*pchisq(Tlr398,df=1)-(0.5-q)*pchisq(Tlr398,df=2) 
Tlr_pval398
Tw398; Tlr398

## naive method 
full_iteration = 1
for(full_iteration in 1:100)
{ 
  if(full_iteration==1) 
  { 
    nls_for_initial   = nls(logrna~log10(exp(p1-lamb1*day_rescal)+exp(p2-lamb2*day_rescal)),data=dat,start=list(p1=10,lamb1=68,p2=7,lamb2=1)) 
    start2 = summary(nls_for_initial)$coef[,1]
    dat = groupedData(logrna~1|id,data=dat)
    fm1 =  nlme(logrna~log10(exp(P1-lamb1*day_rescal)+exp(P2-lamb2*day_rescal)),  data = dat,  fixed = P1+lamb1+P2+lamb2 ~ 1, random = P1+lamb1+P2+lamb2~1,   start =start2,verbose=TRUE,control=nlmeControl(maxIter=1, pnlsMaxIter=2000, msMaxIter=500, minScale=1e-7,  tolerance=0.98, niterEM=1000, pnlsTol=5e-3, msTol=1e-7, returnObject=TRUE, msVerbose=FALSE))
    m = length(unique(dat$id) )
    bi_estimate=as.data.table(fm1$coefficients$random$id)
    bi_estimate[,id:=as.numeric(rownames(fm1$coefficients$random$id))]
    bi_estimate = bi_estimate[order(id)]
    beta_old = fm1$coefficients$fixed
    b_old = matrix(rep(0, 4*m), ncol=m); 
    for(k in 1:m) b_old[,k] = as.numeric(bi_estimate[k,1:4])
  } 
  cluster_dt = as.data.table(dat)[,.N,by=id][order(as.numeric(as.character(id)))]; cluster_dt[,cluster:=1:nrow(cluster_dt)] 
  dat2=merge(as.data.table(dat),cluster_dt[,.(id,cluster)],by.x='id',by.y='id')[order(cluster)]
  y=dat$logrna; cens=rep(0,nrow(dat)); cluster=dat2[,cluster];  x=as.matrix(as.data.frame(dat)[,c('day_rescal')]); fun=biexp; epsilon=1e-3; bi.subset = c(1,2,3,4);  sigma2=0.5;   method="ML"; varstruct="unstructured";  maxstep=2000; verbose=T; epsstop=1e-3 
  beta = beta_old; 
  b = b_old
  r = dim(x)[2]
  m = length(unique(cluster))
  n = length(cluster)
  ni = table(cluster)
  cl = cluster
  p = length(beta)
  q = ifelse(all(bi.subset==0), p, length(bi.subset))
  X = matrix(rep(0,n*p), ncol=p)
  Z = matrix(rep(0,n*q), ncol=q)
  yl = rep(NA,length(y))
  ###### Linearization step
  for (i in 1:m)
  {  
    betai = beta; 
    betai[bi.subset] = betai[bi.subset] + b[,i]
    fx.arg = as.list(c(x[1,], betai))
    for(j in 1:r) fx.arg[[j]] = x[cluster==i,j]
    names(fx.arg) = c(paste("x",1:r,sep=""),paste("beta",1:p,sep=""))
    formals(fun) = fx.arg
    fx = fun()
    X[cluster==i,] = Xi = attr(fx,"gradient")
    Z[cluster==i,] = Zi = Xi[, bi.subset,drop=F]
    yl[cluster==i] = y[cluster==i] - as.numeric(fx) + Xi %*% beta + Zi %*% b[,i]
  }  
  ###### LME step (with order constraints incorporated)
  lme_out398_naive = lmec_Amat_bvec_constraint(yL=yl, cens=cens, X=X, Z=Z, cluster=cluster,init=list(beta=beta,b), maxstep = 200,epsstop = 0.05, abspmv = 0.001, mcmc0 = 100, sdl = 0.1, iter2 = 15, trs = 5, pls = 5, mcmcmax = 1000, Amat=t(rbind(c(0,1,0,0),c(0,0,0,1))),bvec=c(0,0))
  beta_new = lme_out398_naive$beta
  absolute_beta_old_new = abs(beta_old - beta_new)
  relative_beta_old_new = abs(beta_old[beta_old!=0] - beta_new[beta_old!=0])/abs(beta_old[beta_old!=0])
  beta_old = beta_new
  b_new = lme_out398_naive$bi
  b_old = b_new
  cat(paste0('full_iteration=',full_iteration,'; max(abs_beta)=',max(absolute_beta_old_new),'; max(rel_beta)=',max(relative_beta_old_new),'\n'))
  if(max(relative_beta_old_new)<0.001) break;
} 

save(lme_out398,lme_out398_naive,Tw398,Tlr398,Tw_pval398,Tlr_pval398,file='398results')
### table 1
load('315results'); load('398results')
beta_est_MTS_315 = lme_out315$beta 
beta_sd_MTS_315 = sqrt(diag(lme_out315$varFix))
Psi_MTS_315 = lme_out315$Psi
sigma2_MTS_315 = lme_out315$sigma^2

beta_est_naive_315 = lme_out315_naive$beta 
beta_sd_naive_315 = sqrt(diag(lme_out315_naive$varFix))
Psi_naive_315 = lme_out315_naive$Psi
sigma2_naive_315 = lme_out315_naive$sigma^2

beta_est_MTS_398 = lme_out398$beta 
beta_sd_MTS_398 = sqrt(diag(lme_out398$varFix))
Psi_MTS_398= lme_out398$Psi
sigma2_MTS_398= lme_out398$sigma^2

beta_est_naive_398 = lme_out398_naive$beta 
beta_sd_naive_398 = sqrt(diag(lme_out398_naive$varFix))
Psi_naive_398= lme_out398_naive$Psi
sigma2_naive_398= lme_out398_naive$sigma^2

for(k in 1:5) cat(sprintf('%.2f & %.2f & & %.2f & %.2f\n\n',beta_est_MTS_315[k],beta_sd_MTS_315[k],beta_est_naive_315[k],beta_sd_naive_315[k]))
 
for(k in 1:4) cat(sprintf('%.2f & %.2f & & %.2f & %.2f\n\n',beta_est_MTS_398[k],beta_sd_MTS_398[k],beta_est_naive_398[k],beta_sd_naive_398[k]))

### table 2
cat(sprintf('%.1f & %.1f &   %.1f & %.1f\n\n',Psi_MTS_315[1,1],Psi_MTS_315[1,2],Psi_MTS_315[1,3],Psi_MTS_315[1,4]))
cat(sprintf('. & %.1f &   %.1f & %.1f\n\n',Psi_MTS_315[2,2],Psi_MTS_315[2,3],Psi_MTS_315[2,4]))
cat(sprintf('. & . &   %.1f & %.1f\n\n',Psi_MTS_315[3,3],Psi_MTS_315[3,4]))
cat(sprintf('. & . &   . & %.1f\n\n',Psi_MTS_315[4,4] ))
round(Psi_MTS_315,1)
sprintf('%.2f',sigma2_MTS_315)

cat(sprintf('%.1f & %.1f &   %.1f & %.1f\n\n',Psi_naive_315[1,1],Psi_naive_315[1,2],Psi_naive_315[1,3],Psi_naive_315[1,4]))
cat(sprintf('. & %.1f &   %.1f & %.1f\n\n',Psi_naive_315[2,2],Psi_naive_315[2,3],Psi_naive_315[2,4]))
cat(sprintf('. & . &   %.1f & %.1f\n\n',Psi_naive_315[3,3],Psi_naive_315[3,4]))
cat(sprintf('. & . &   . & %.1f\n\n',Psi_naive_315[4,4] ))
round(Psi_naive_315,1)
sprintf('%.2f',sigma2_naive_315)


cat(sprintf('%.1f & %.1f &   %.1f & %.1f\n\n',Psi_MTS_398[1,1],Psi_MTS_398[1,2],Psi_MTS_398[1,3],Psi_MTS_398[1,4]))
cat(sprintf('. & %.1f &   %.1f & %.1f\n\n',Psi_MTS_398[2,2],Psi_MTS_398[2,3],Psi_MTS_398[2,4]))
cat(sprintf('. & . &   %.1f & %.1f\n\n',Psi_MTS_398[3,3],Psi_MTS_398[3,4]))
cat(sprintf('. & . &   . & %.1f\n\n',Psi_MTS_398[4,4] ))
round(Psi_MTS_398,1)
sprintf('%.2f',sigma2_MTS_398)

cat(sprintf('%.1f & %.1f &   %.1f & %.1f\n\n',Psi_naive_398[1,1],Psi_naive_398[1,2],Psi_naive_398[1,3],Psi_naive_398[1,4]))
cat(sprintf('. & %.1f &   %.1f & %.1f\n\n',Psi_naive_398[2,2],Psi_naive_398[2,3],Psi_naive_398[2,4]))
cat(sprintf('. & . &   %.1f & %.1f\n\n',Psi_naive_398[3,3],Psi_naive_398[3,4]))
cat(sprintf('. & . &   . & %.1f\n\n',Psi_naive_398[4,4] ))
round(Psi_naive_398,1)
sprintf('%.2f',sigma2_naive_398)
 