################################################################################
#
# This code is related to the numerical experiments of the article:
# Gomes, E.S. Cruz, F.R.B. (2026) Novel Sampling Strategy for Classical Inference 
# in M/M/1 Queues, Operations Research Letters 67:107461.
#
# (c) 2026, Gomes & Cruz.
# v.2026.03.13
#
################################################################################

rm(list=ls())

library(this.path) # use relative path
setwd(this.path::here())

# remove all variables, except functions
rem_var <- function() {
  all_objects <- ls(envir = .GlobalEnv)
  functions <- all_objects[sapply(all_objects,
                            function(x) is.function(get(x, envir = .GlobalEnv)))]
  rm(list = setdiff(all_objects, functions), envir = .GlobalEnv)
}

lq_mm1 <- function(p){
  return(p^2 / (1-p))
}

ls_mm1 <- function(p){
  return(p / (1-p))
}

monte_carlo <- function(p, n, rep, fest, ...) {
  set.seed(2024)
  samp <- rsamp(p, n, rep)[['samples']]
  est <- apply(samp, 1, fest, ...)    
  return(c(mean(est), sd(est)))
}

monte_carlo_tab <- function(p, n, rep, fest, ...) {
  tab <- matrix(
    nrow = length(p) * length(n),
    ncol = 4,
    dimnames = list(NULL, c('p', 'size', 'mean', 'sd'))
    )
  for (i in 1:length(p)) {
    for (j in 1:length(n)) {
      est <- c(p[i], n[j], monte_carlo(p[i], n[j], rep, fest, ...))
      tab[(i - 1) * length(n) + j,] <- est
    }
  }
  return(tab)
}

monte_carlo_tab_cond <- function(p, n, rep, fest, ...) {
  monte_carlo_cond <- function(p, n, rep, fest, ...) {
    set.seed(2024)
    est <- numeric(rep)
    sim <- rsamp(p, n, rep)
    samp <- sim[['samples']]
    L0 <- sim[['L0']]
    for(i in 1:rep){
      est[i] <- fest(samp[i,], L0[i], ...)
    }
    return(c(mean(est), sd(est)))
  }
  
  tab <- matrix(
    nrow = length(p) * length(n),
    ncol = 4,
    dimnames = list(NULL, c('p', 'size', 'mean', 'sd'))
  )
  for (i in 1:length(p)) {
    for (j in 1:length(n)) {
      est <- c(p[i], n[j], monte_carlo_cond(p[i], n[j], rep, fest, ...))
      tab[(i - 1) * length(n) + j,] <- est
    }
  }
  return(tab)
}

################################################################################
# generating samples
################################################################################

# generates mm1 services
# generates a random number of services during interarrival time tc
# given that the previous customer finds L in the system upon arrival
num_serv_arr <- function(p, L, tc, mu){
  serv_time_accum <- 0
  num_serv <- 0
  while(serv_time_accum <= tc){
    serv_time_accum <- serv_time_accum + rexp(1, rate=mu)
    if(serv_time_accum <= tc) num_serv <- num_serv + 1
    if(num_serv == L+1) break # we can service at most L+1 customers
  }
  return(num_serv)
}

# generates rep random successive mm1 samples of size n
rsamp <- function(p, n, rep){
  lambda <- 1
  mu <- lambda/p
  L0 <- rgeom(rep, prob=1-p) # number of customers at 0st customer arrival
  samples <- matrix(NA, nrow=rep, ncol=n)
  for(i in 1:rep){
    tc <- rexp(n, rate=lambda)
    num_serv <- numeric(n)
    Lj <- L0[i] 
    for(j in 1:n){
      num_serv[j] <- num_serv_arr(p, Lj, tc[j], mu)
      Lj <- L0[i] + j - sum(num_serv) # iterate to find next Lj
    }
    samples[i,] <- num_serv
  }
  return(list(samples=samples, L0=L0))
}

################################################################################
# probability mass function
################################################################################

# unconditional probability mass function
pmf <- function(x, p){
  return((p/(1+p))^(x+1) + (1-p)/p * (p/(1+p))^x * (x!=0))
}

# conditional probability mass function 
# given that the previous customer find L in the system upon arrival
pmf_cond <- function(x, p, L){
  return((1+p)^(-x) * (p/(1+p))^(x<=L) * (x <= L+1))
}

################################################################################
# likelihood function
################################################################################

lik <- function(samp, p){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  dm <- max(delta)
  tm <- sum(delta < dm)
  return(p^dm / (1+p)^s[n] * ((1-p) * (p/(1+p))^tm + p * (p/(1+p))^n))
}

loglik <- function(samp, p){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  dm <- max(delta)
  tm <- sum(delta < dm)
  return(dm*log(p) - s[n]*log(1+p) + log((1-p) * (p/(1+p))^tm +
                                           p * (p/(1+p))^n))
}

mle_p <- function(samp, tol=1e-3){
  loglik_aux <- function(p){
    loglik(samp, p)
  }
  mle <- optimize(loglik_aux, lower=tol, upper=1-tol, maximum=T)
  return(as.numeric(mle$maximum))
}

mle_lq <- function(samp, tol){
  pest <- mle_p(samp, tol)
  return(lq_mm1(pest))
}

mle_ls <- function(samp, tol){
  pest <- mle_p(samp, tol)
  return(ls_mm1(pest))
}

lik_cond <- function(samp, p, L){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  tL <- sum(delta < L)
  hL <- prod(delta < L+1)
  return((1+p)^(-s[n]) * (p/(1+p))^tL * hL)
}

mle_p_cond <- function(samp, L, tol=1e-3){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  tL <- sum(delta < L)
  return(min(tL/s[n], 1-tol))
}

mle_lq_cond <- function(samp, L, tol){
  pest <- mle_p_cond(samp, L, tol)
  return(lq_mm1(pest))
}

mle_ls_cond <- function(samp, L, tol){
  pest <- mle_p_cond(samp, L, tol)
  return(ls_mm1(pest))
}

################################################################################
# conditional beta self
################################################################################

gauhyp <- function(a, b, c, z){
  faux <- function(p){
    return(p^(b-1) * (1-p)^(c-b-1) * (1-z*p)^(-a))
  }
  return(integrate(faux, 0, 1)[[1]] / beta(b, c-b))
}

beta_pri <- function(p, a, b){
  return(p^(a-1) * (1-p)^(b-1))
}

beta_post_cond_kernel <- function(p, samp, L, a, b){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  gL <- sum(delta < L)
  return(p^(a+gL-1) * (1-p)^(b-1) *(1+p)^(-s[n]-gL))
}

beta_post_cond <- function(p, samp, L, a, b){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  gL <- sum(delta < L)
  const_norm <- beta(a+gL, b) * gauhyp(s[n]+gL, a+gL, a+gL+b, -1)
  return(beta_post_cond_kernel(p, samp, L, a, b) / const_norm)
}

beta_p_cond <- function(samp, L, a, b){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  gL <- sum(delta < L)
  const_norm <- beta(a+gL, b) * gauhyp(s[n]+gL, a+gL, a+gL+b, -1)
  faux <- function(p){
    return(beta_post_cond_kernel(p, samp, L, a, b) * p)
  }
  return(integrate(faux, 0, 1)[[1]] / const_norm)
}

beta_lq_cond <- function(samp, L, a, b, tol=0.1){
  # renormalization performed after the integration for efficiency
  pmax = 1-tol
  faux <- function(p){
    return(beta_post_cond_kernel(p, samp, L, a, b) * lq_mm1(p))
  }
  const_norm <- integrate(beta_post_cond_kernel, 0, pmax, samp, L, a, b)[[1]]
  return(integrate(faux, 0, pmax)[[1]] / const_norm)
}

beta_ls_cond <- function(samp, L, a, b, tol=0.1){
  # renormalization performed after the integration for efficiency
  pmax = 1-tol
  faux <- function(p){
    return(beta_post_cond_kernel(p, samp, L, a, b) * ls_mm1(p))
  }
  const_norm <- integrate(beta_post_cond_kernel, 0, pmax, samp, L, a, b)[[1]]
  return(integrate(faux, 0, pmax)[[1]] / const_norm)
}

################################################################################
# beta self
################################################################################

beta_post_kernel <- function(p, samp, a, b){
  n <- length(samp)
  s <- cumsum(samp)
  delta <- s - (1:n)
  dm <- max(delta)
  gm <- sum(delta < dm)
  return(p^(a+dm+gm-1) * (1+p)^(-s[n]-gm) * (1-p)^(b-1) * 
             ((1-p) + p*(p/(1+p))^(n-gm)))
}

beta_post <- function(p, samp, a, b){
  const_norm <- integrate(beta_post_kernel, 0, 1, samp, a, b)[[1]] 
  return(beta_post_kernel(p, samp, a, b) / const_norm)  
}

beta_p <- function(samp, a, b, tol=1e-4){
  pmax <- 1-tol
  faux <- function(p){
    return(beta_post_kernel(p, samp, a, b) * p)
  }
  const_norm <- integrate(beta_post_kernel, 0, pmax, samp, a, b)[[1]]
  return(integrate(faux, 0, pmax)[[1]] / const_norm)
}

beta_lq <- function(samp, a, b, tol=0.1){
  # renormalization performed after the integration for efficiency
  pmax = 1-tol
  faux <- function(p){
    return(beta_post_kernel(p, samp, a, b) * lq_mm1(p))
  }
  const_norm <- integrate(beta_post_kernel, 0, pmax, samp, a, b)[[1]]
  return(integrate(faux, 0, pmax)[[1]] / const_norm)
}

beta_ls <- function(samp, a, b, tol=0.1){
  # renormalization performed after the integration for efficiency
  pmax = 1-tol
  faux <- function(p){
    return(beta_post_kernel(p, samp, a, b) * ls_mm1(p))
  }
  const_norm <- integrate(beta_post_kernel, 0, pmax, samp, a, b)[[1]]
  return(integrate(faux, 0, pmax)[[1]] / const_norm)
}

################################################################################
# alternative scheme 1 - arrivals during service (ads)
################################################################################

ads_mle_p <- function(ads_samp, tol = 1e-3){
  return(min(mean(ads_samp), 1-tol))
}

ads_mle_lq <- function(ads_samp, tol){
  pest <- ads_mle_p(ads_samp, tol)
  return(lq_mm1(pest))
}

ads_mle_ls <- function(ads_samp, tol){
  pest <- ads_mle_p(ads_samp, tol)
  return(ls_mm1(pest))
}

ads_monte_carlo <- function(p, n, rep, fest, ...) {
  set.seed(2024)
  ads_samp <- t(replicate(rep, rgeom(n, prob = 1 / (1 + p))))
  est <- apply(ads_samp, 1, fest, ...)    
  return(c(mean(est), sd(est)))
}

ads_monte_carlo_tab <- function(p, n, rep, fest, ...) {
  tab <- matrix(
    nrow = length(p) * length(n),
    ncol = 4,
    dimnames = list(NULL, c('p', 'size', 'mean', 'sd'))
  )
  for (i in 1:length(p)) {
    for (j in 1:length(n)) {
      est <- c(p[i], n[j], ads_monte_carlo(p[i], n[j], rep, fest, ...))
      tab[(i - 1) * length(n) + j,] <- est
    }
  }
  return(tab)
}

################################################################################
# alternative sample scheme 2 - size at departures (sdep)
################################################################################

#  simulates a random g-g-c queue
rggc <- function(size_max, nserv, farr, fdep, narr_sim){
  # todo: implement finite queues
  
  # initialize variables
  arr <- cumsum(sapply(1:narr_sim, farr))
  dep <- sapply(1:narr_sim, fdep)
  serv_free <- rep(0, nserv)
  arr_start_serv <- rep(0, narr_sim)
  arr_end_serv <- rep(0, narr_sim)
  
  # simulate end of service times
  for(i in 1:narr_sim){
    k_next <- which.min(serv_free)
    arr_start_serv[i] <- max(arr[i], serv_free[k_next])
    arr_end_serv[i] <- arr_start_serv[i] + dep[i]
    serv_free[k_next] <- arr_end_serv[i]
  }
  
  # update queue
  queue_tab <- data.frame(
    time = c(arr, arr_end_serv),
    type = c(rep('a', length(arr)), rep('d', length(arr_end_serv)))
  )
  queue_tab <- queue_tab[order(queue_tab$time), ]
  queue_tab$size <- cumsum(ifelse(queue_tab$type == 'a', 1, -1))
  
  return(queue_tab)
}

get_trans_count <- function(sizes_seq){
  max_state <- max(1, max(sizes_seq))
  i <- sizes_seq[-length(sizes_seq)]
  j <- sizes_seq[-1]
  tab <- table(factor(i, 0:max_state), factor(j, 0:max_state))
  return(as.matrix(tab))
}

sdep_mle_p <- function(sdep_samp, tol = 1e-3){
  n0 <- sdep_samp[1]
  trans_count <- get_trans_count(sdep_samp)
  m <- nrow(trans_count) - 1
  n00 <- sum(trans_count[1, ])
  n10 <- sum(trans_count[2, ])
  N <- 0
  
  S1 <- 0
  if(m >= 2){
    for(i in 2:m){
      for(j in (i-1):m){
        nij <- trans_count[i+1, j+1]
        N <- N + nij
        S1 <- S1 + (j - i + 1) * nij
      }
    }
  }
  
  S2 <- 0
  for(j in 0:m){
    S2 <- S2 + j * (trans_count[1, j+1] + trans_count[2, j+1])
  }
  A <- N + n00 + n10 - n0 - 1
  B <- N + S1 + n00 + n10 + S2 + 1
  C <- n0 + S2 + S1
  rho_hat <- (B - sqrt(B^2 - 4*A*C)) / (2*A)
  
  return(min(rho_hat, 1 - tol))
}

sdep_mle_lq <- function(sdep_samp, tol){
  pest <- sdep_mle_p(sdep_samp, tol)
  return(lq_mm1(pest))
}

sdep_mle_ls <- function(sdep_samp, tol){
  pest <- sdep_mle_p(sdep_samp, tol)
  return(ls_mm1(pest))
}

sdep_monte_carlo <- function(p, n, rep, fest, ...) {
  set.seed(2024)
  burn_in <- 1000
  est <- replicate(rep, {
    sim_queue <- rggc(
      size_max = 1000,
      nserv = 1,
      farr = function(x) rexp(n = 1, rate = 1),
      fdep = function(x) rexp(n = 1, rate = 1/p),
      narr_sim = n + burn_in
    )
    
    sim_queue <- sim_queue[(burn_in + 1):nrow(sim_queue), ]
    sdep_samp <- sim_queue$size[sim_queue$type == "d"]
    fest(sdep_samp, ...)
  })
  c(mean(est), sd(est))
}

sdep_monte_carlo_tab <- function(p, n, rep, fest, ...) {
  tab <- matrix(
    nrow = length(p) * length(n),
    ncol = 4,
    dimnames = list(NULL, c("p", "size", "mean", "sd"))
  )
  for (i in 1:length(p)) {
    for (j in 1:length(n)) {
      est <- c(p[i], n[j], sdep_monte_carlo(p[i], n[j], rep, fest, ...))
      tab[(i - 1) * length(n) + j, ] <- est
    }
  }
  return(tab)
}

################################################################################
# simulation
################################################################################

today <-  format(Sys.Date(), "%d-%m-%Y")
p <- c(0.01, 0.1, 0.2, 0.5, 0.8, 0.9, 0.99)
p_lq <- c(0.1, 0.2, 0.5, 0.7, 0.8, 0.85) # lq up to 5
p_ls <- c(0.1, 0.2, 0.5, 0.7, 0.8, 0.83) # ls up to 5
tol <- 0.1 # only for lq and ls
n <- c(10, 20, 50, 100, 200, 500)
rep <- 1000

# maximum likelihood
sim_mle_p <- monte_carlo_tab(p, n, rep, mle_p)
sim_mle_p_cond <- monte_carlo_tab_cond(p, n, rep, mle_p_cond)

sim_mle_lq <- monte_carlo_tab(p_lq, n, rep, mle_lq, tol)
sim_mle_lq_cond <- monte_carlo_tab_cond(p_lq, n, rep, mle_lq_cond, tol)

sim_mle_ls <- monte_carlo_tab(p_ls, n, rep, mle_ls, tol)
sim_mle_ls_cond <- monte_carlo_tab_cond(p_ls, n, rep, mle_ls_cond, tol)

save(p, p_lq, p_ls, n, tol, rep,
     sim_mle_p, sim_mle_p_cond,
     sim_mle_lq, sim_mle_lq_cond,
     sim_mle_ls, sim_mle_ls_cond,
     file=paste0('results/simulation_mle_', today,'.rdata'))

# arrivals during service
sim_ads_p <- ads_monte_carlo_tab(p, n, rep, ads_mle_p)
sim_ads_lq <- ads_monte_carlo_tab(p_lq, n, rep, ads_mle_lq, tol)
sim_ads_ls <- ads_monte_carlo_tab(p_ls, n, rep, ads_mle_ls, tol)


save(p, p_lq, p_ls, n, tol, rep,
     sim_ads_p,
     sim_ads_lq,
     sim_ads_ls,
     file=paste0('results/simulation_ads_', today,'.rdata'))

# size at departures
sim_sdep_p <- sdep_monte_carlo_tab(p, n, rep, sdep_mle_p)
sim_sdep_lq <- sdep_monte_carlo_tab(p_lq, n, rep, sdep_mle_lq, tol)
sim_sdep_ls <- sdep_monte_carlo_tab(p_ls, n, rep, sdep_mle_ls, tol)

save(p, p_lq, p_ls, n, tol, rep,
     sim_sdep_p,
     sim_sdep_lq,
     sim_sdep_ls,
     file=paste0('results/simulation_sdep_', today,'.rdata'))


# beta 1 - uniform prior
a1 <- 1
b1 <- 1

sim_beta1_p <- monte_carlo_tab(p, n, rep, beta_p, a1, b1)
sim_beta1_p <- monte_carlo_tab(p, n, rep, beta_p, a1, b1)
sim_beta1_p_cond <- monte_carlo_tab_cond(p, n, rep, beta_p_cond, a1, b1)

sim_beta1_lq <- monte_carlo_tab(p_lq, n, rep, beta_lq, a1, b1, tol)
sim_beta1_lq_cond <- monte_carlo_tab_cond(p_lq, n, rep, beta_lq_cond, a1, b1, tol)

sim_beta1_ls <- monte_carlo_tab(p_ls, n, rep, beta_ls, a1, b1, tol)
sim_beta1_ls_cond <- monte_carlo_tab_cond(p_ls, n, rep, beta_ls_cond, a1, b1, tol)

save(p, p_lq, p_ls, n, tol, rep, a1, b1,
     sim_beta1_p, sim_beta1_p_cond,
     sim_beta1_lq, sim_beta1_lq_cond,
     sim_beta1_ls, sim_beta1_ls_cond,
     file=paste0('results/simulation_beta1_', today,'.rdata'))

# beta 2 - light loaded queue
a2 <- 1.5
b2 <- 2.5

sim_beta2_p <- monte_carlo_tab(p, n, rep, beta_p, a2, b2)
sim_beta2_p_cond <- monte_carlo_tab_cond(p, n, rep, beta_p_cond, a2, b2)

sim_beta2_lq <- monte_carlo_tab(p_lq, n, rep, beta_lq, a2, b2, tol)
sim_beta2_lq_cond <- monte_carlo_tab_cond(p_lq, n, rep, beta_lq_cond, a2, b2, tol)

sim_beta2_ls <- monte_carlo_tab(p_ls, n, rep, beta_ls, a2, b2, tol)
sim_beta2_ls_cond <- monte_carlo_tab_cond(p_ls, n, rep, beta_ls_cond, a2, b2, tol)

save(p, p_lq, p_ls, n, tol, rep, a2, b2,
     sim_beta2_p, sim_beta2_p_cond,
     sim_beta2_lq, sim_beta2_lq_cond,
     sim_beta2_ls, sim_beta2_ls_cond,
     file=paste0('results/simulation_beta2_', today,'.rdata'))

# beta 3 - heavy loaded queue
a3 <- 2.5
b3 <- 1.5

sim_beta3_p <- monte_carlo_tab(p, n, rep, beta_p, a3, b3)
sim_beta3_p_cond <- monte_carlo_tab_cond(p, n, rep, beta_p_cond, a3, b3)

sim_beta3_lq <- monte_carlo_tab(p_lq, n, rep, beta_lq, a3, b3, tol)
sim_beta3_lq_cond <- monte_carlo_tab_cond(p_lq, n, rep, beta_lq_cond, a3, b3, tol)

sim_beta3_ls <- monte_carlo_tab(p_ls, n, rep, beta_ls, a3, b3, tol)
sim_beta3_ls_cond <- monte_carlo_tab_cond(p_ls, n, rep, beta_ls_cond, a3, b3, tol)

save(p, p_lq, p_ls, n, tol, rep, a3, b3,
     sim_beta3_p, sim_beta3_p_cond,
     sim_beta3_lq, sim_beta3_lq_cond,
     sim_beta3_ls, sim_beta3_ls_cond,
     file=paste0('results/simulation_beta3_', today,'.rdata'))
rem_var()


################################################################################
# tests
################################################################################

# testing number of services during arrivals generator -------------------------
lambda <- 1
p <- 0.8
mu <- lambda/p
l <- 3
rep <- 1e6
possible_values <- seq(0,l+1)
num_serv <- numeric(rep)
for(i in 1:rep){
  num_serv[i] <- num_serv_arr(p, l, 1, mu)
}
# fixed tc = 1, v.a ~ poisson(mu*1)
# those values must be approximately equal
round(table(num_serv)/rep,4)
round(dpois(possible_values, mu) / ppois(l+1, mu),4) # a truncated poisson
rem_var()


# testing pmf and moments ------------------------------------------------------
p <- 0.55
lambda <- 1
mu <- lambda/p
rep <- 1e6
L <- rgeom(rep, prob = 1 - p)
tc <- rexp(rep, rate=lambda)
num_serv <- numeric(rep)
for(i in 1:rep){
  num_serv[i] <- num_serv_arr(p, L[i], tc[i], mu)
}
# mean: those values must be approximately equal
mean(num_serv)
1
# variance: those values must be approximately equal
var(num_serv)
2*p
# those values must be approximately equal
round(head(table(num_serv), 10+1)/rep,4)
round(pmf(0:10, p),4) # first terms of pmf
rem_var()


# testing conditional pmf and moments ------------------------------------------
p <- 0.85
lambda <- 1
mu <- lambda/p
rep <- 1e6
L <- 5
tc <- rexp(rep, rate=lambda)
num_serv <- numeric(rep)
for(i in 1:rep){
  num_serv[i] <- num_serv_arr(p, L, tc[i], mu)
}
# those values must be approximately equal
round(head(table(num_serv), 10+1)/rep,4)
round(pmf_cond(0:10, p, L),4) # first terms of conditional pmf
rem_var()


# testing frequencies generated by rsamp ---------------------------------------
p <- 0.55
n <- 100
rep <- 1e4
samples <- rsamp(p, n, rep)
# those values must be approximately equal
round(table(samples$samples)/(rep*n),4)
round(pmf(0:15, p),4)
rem_var()


# testing mle ------------------------------------------------------------------
p <- 0.80
n <- 500
rep <- 1e3
samples <- rsamp(p, n, rep)[['samples']]
est_p <- apply(samples, 1, function(samp) mle_p(samp))
est_lq <- apply(samples, 1, function(samp) mle_lq(samp, tol=0.1))
est_ls <- apply(samples, 1, function(samp) mle_ls(samp, tol=0.1))

hist(est_p, col=rgb(1, 0, 0, 0.5), probability = T, xlim=c(0,1), main='mle p')
abline(v=p, lwd=3, col='black')
hist(est_lq, col=rgb(1, 0, 0, 0.5), probability = T,  main='mle lq')
abline(v=lq_mm1(p), lwd=3, col='black')
hist(est_ls, col=rgb(1, 0, 0, 0.5), probability = T, main='mle ls')
abline(v=ls_mm1(p), lwd=3, col='black')
rem_var()
dev.off()

# testing conditional mle ------------------------------------------------------
p <- 0.82
n <- 500
rep <- 1e4
sim <- rsamp(p, n, rep)
samp <- sim[['samples']]
L0 <- sim[['L0']]
est_p <- numeric(rep)
est_lq <- numeric(rep)
est_ls <- numeric(rep)
for(i in 1:rep){
  est_p[i] <- mle_p_cond(samp[i,], L0[i])
  est_lq[i] <- mle_lq_cond(samp[i,], L0[i], tol=0.1)
  est_ls[i] <- mle_ls_cond(samp[i,], L0[i], tol=0.1)
}

hist(est_p, col=rgb(1, 0, 0, 0.5), probability = T, xlim=c(0,1), main='mle p')
abline(v=p, lwd=3, col='black')
hist(est_lq, col=rgb(1, 0, 0, 0.5), probability = T, main='mle lq')
abline(v=lq_mm1(p), lwd=3, col='black')
hist(est_ls, col=rgb(1, 0, 0, 0.5), probability = T, main='mle ls')
abline(v=ls_mm1(p), lwd=3, col='black')

rem_var()
dev.off()

# testing beta prior -----------------------------------------------------------
a <- c(0.5, 1, 1.5, 2, 2.5)
b <- c(0.5, 1.5, 1, 2, 1)
error <- numeric(length(a))
for(i in 1:length(a)){
  error[i] <- integrate(beta_pri, 0, 1, a[i], b[i])[[1]] - beta(a[i], b[i])
}
max(abs(error)) # must be near 0
rem_var()

# testing conditional beta posterior -------------------------------------------
a <- runif(1, 0.5, 5)
b <- runif(1, 0.5, 5)
p <- 0.2
n <- 50
sim <- rsamp(p, n, 1)
samp <- sim$samples[1,]
L <- sim$L0
fteo <- function(p, samp, L, a, b){
  return(lik_cond(samp, p, L) * beta_pri(p, a, b))
}
pseq <- seq(0.01, 0.99, 1e-2)
error <- numeric(length(pseq))
for(i in 1:length(pseq)){
  error[i] <- beta_post_cond(pseq[i], samp, L, a, b) - 
    fteo(pseq[i], samp, L, a, b) / integrate(fteo, 0, 1, samp, L, a, b)[[1]]
}
max(abs(error)) # must be near 0
plot(pseq, beta_post_cond(pseq, samp, L, a, b), 'l')
plot(pseq, lik_cond(samp, pseq, L), 'l')
plot(pseq, abs(error), 'l')
rm(fteo)
rem_var()


# testing beta posterior -------------------------------------------------------
a <- runif(1, 0.5, 5)
b <- runif(1, 0.5, 5)
p <- 0.7
n <- 500
sim <- rsamp(p, n, 1)
samp <- sim$samples
faux <- function(p, samp, a, b){
  return(lik(samp, p) * beta_pri(p, a, b))
}
pseq <- seq(0.01, 0.99, 1e-2)
error <- numeric(length(pseq))
for(i in 1:length(pseq)){
  error[i] <- beta_post(pseq[i], samp, a, b) - 
    faux(pseq[i], samp, a, b) / integrate(faux, 0, 1, samp, a, b)[[1]]
}
plot(pseq, lik(samp, pseq), 'l' )
max(abs(error)) # must be near 0
rm(faux)
rem_var()


# testing conditional beta self estimators -------------------------------------
a <- runif(1, 0.5, 5)
b <- runif(1, 0.5, 5)
p <- 0.8
n <- 500
rep <- 1000
#error <- numeric(rep)
est_p <- numeric(rep)
est_lq <- numeric(rep)
est_ls <- numeric(rep)
for(i in 1:rep){
  sim <- rsamp(p, n, 1)
  samp <- sim$samples[1,]
  Linit <- sim$L0
  est_p[i] <-  beta_p_cond(samp, Linit, a, b)
  est_lq[i] <-  beta_lq_cond(samp, Linit, a, b)
  est_ls[i] <-  beta_ls_cond(samp, Linit, a, b)
  #error[i] <- est[i] - p
}

# estimator for p
hist(est_p, xlim = c(0, 1))
abline(v=p, lwd=3, col='black')
mean(est_p)-p # bias
sd(est_p)
# estimator for lq
hist(est_lq)
abline(v=lq_mm1(p), lwd=3, col='black')
mean(est_lq)-lq_mm1(p) # bias
sd(est_lq)
# estimator for ls
hist(est_ls)
abline(v=ls_mm1(p), lwd=3, col='black')
mean(est_ls)-ls_mm1(p) # bias
sd(est_ls)
rem_var()

# testing beta self estimators -------------------------------------------------
a <- runif(1, 0.5, 5)
b <- runif(1, 0.5, 5)
p <- 0.8
n <- 500
rep <- 1000
#error <- numeric(rep)
est_p <- numeric(rep)
est_lq <- numeric(rep)
est_ls <- numeric(rep)
for(i in 1:rep){
  sim <- rsamp(p, n, 1)
  samp <- sim$samples[1,]
  est_p[i] <-  beta_p(samp, a, b)
  est_lq[i] <-  beta_lq(samp, a, b)
  est_ls[i] <-  beta_ls(samp, a, b)
}

# estimator for p
hist(est_p, xlim = c(0, 1))
abline(v=p, lwd=3, col='black')
mean(est_p)-p # bias
sd(est_p)
# estimator for lq
hist(est_lq)
abline(v=lq_mm1(p), lwd=3, col='black')
mean(est_lq)-lq_mm1(p) # bias
sd(est_lq)
# estimator for ls
hist(est_ls)
abline(v=ls_mm1(p), lwd=3, col='black')
mean(est_ls)-ls_mm1(p) # bias
sd(est_ls)
rem_var()

# testing random ggc generator -------------------------------------------------
nserv <- 1
rho <- 0.80
repet <- 100
erro_rho <- numeric(repet)
erro_Ls <- numeric(repet)
erro_Lq <- numeric(repet)

mmc_P0 <- function(rho, c){
  a <- c * rho
  invP0 <- sum(sapply(0:(c-1), function(n) a^n / factorial(n))) +
    (a^c / factorial(c)) * (1 / (1 - rho))
  return(1 / invP0)
}

mmc_Lq_rho <- function(rho, c){
  a <- c * rho
  P0 <- mmc_P0(rho, c)
  return((P0 * a^c * rho) / (factorial(c) * (1 - rho)^2))
}

mmc_Ls_rho <- function(rho, c){
  return(mmc_Lq_rho(rho, c) + c * rho)
}

for(i in 1:repet){
  sim_queue <- rggc(
    size_max = 1000,
    nserv = nserv,
    farr = function(x) rexp(n = 1, rate = 1),
    fdep = function(x) rexp(n = 1, rate = 1/(nserv * rho)),
    narr_sim = 20e3
  )
  sim_queue$gap <- c(diff(sim_queue$time), 0)
  Ls_teo <- mmc_Ls_rho(rho, c = nserv)
  Ls_est <- sum(sim_queue$size * sim_queue$gap) / sum(sim_queue$gap)
  erro_Ls[i] <- Ls_est - Ls_teo
  
  # performance measures
  total_serv_time <- sum(sim_queue$gap * pmin(sim_queue$size, nserv))
  total_time <- sum(sim_queue$gap)
  rho_est <- total_serv_time / (nserv * total_time)
  erro_rho[i] <- rho_est - rho
  
  sim_queue$size_queue <- pmax(sim_queue$size - nserv, 0)
  Lq_teo <- mmc_Lq_rho(rho, c = nserv)
  Lq_est <- sum(sim_queue$size_queue * sim_queue$gap) / sum(sim_queue$gap)
  erro_Lq[i] <- Lq_est - Lq_teo
}

mean(erro_rho)
mean(erro_Lq)
mean(erro_Ls)
sd(erro_rho)
sd(erro_Lq)
sd(erro_Ls)
rem_var()

# testing get_trans_count matrix function --------------------------------------
nserv <- 1
rho <- 0.80
repet <- 100
sim_queue <- rggc(
  size_max = 1000,
  nserv = nserv,
  farr = function(x) rexp(n = 1, rate = 1),
  fdep = function(x) rexp(n = 1, rate = 1/(nserv * rho)),
  narr_sim = 20e3
)
trans_count <- get_trans_count(sim_queue$size) # birth-death
trans_count
rem_var()

# testing sdep-mle -------------------------------------------------------------
nserv <- 1
rho <- 0.85
repet <- 100
burn_in <- 100
sim_queue <- rggc(
  size_max = 1000,
  nserv = nserv,
  farr = function(x) rexp(n = 1, rate = 1),
  fdep = function(x) rexp(n = 1, rate = 1/(nserv * rho)),
  narr_sim = 20e3
)
sim_queue <- sim_queue[(burn_in + 1):nrow(sim_queue),]
sdep_samp <- sim_queue$size[sim_queue$type == 'd']
sdep_mle_p(sdep_samp)
rem_var()
