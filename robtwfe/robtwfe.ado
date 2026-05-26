*! version 1.0.9 20260321 David Veenman

/*
20260321: 1.0.9     Removed reliance on robreg for part of Pseudo R2 calculation
20260320: 1.0.8     Fixed minor stability issues 
20260226: 1.0.7     Made SE clustering optional to allow for non-clustered robust standard errors
20260225: 1.0.6     Small correction in dof calculation with collinear variables + some minor housekeeping 
20260220: 1.0.5     Speed improvement: replaced first-step MM-QR estimation to allow for multiple fixed effects 
20260213: 1.0.4     Return scale parameter 
20260111: 1.0.3     Small bug fix for handling missing values in absorbed time variable
20260110: 1.0.2     Small bug fix for older Stata versions, plus added checks for non-binary DV and nested FEs
20251230: 1.0.1     Made areg default given faster execution, reghdfe is used for Stata versions below 19
20251224: 1.0.0     First version

Dependencies:
   moremata
   reghdfe
   hdfe
*/

program define robtwfe, eclass sortpreserve
	version 15
	syntax [anything] [in] [if], ivar(str) tvar(str) eff(real) [cluster(varlist) tol(real 0) weightvar(str)]
	
	capt findfile mf_mm_aqreg.hlp
	if _rc {
		di as error "Program requires the {bf:moremata} package: type {stata ssc install moremata, replace}"
		error 499
	}

	capt findfile reghdfe.ado 
	if _rc {
		di as error "Program requires the {bf:reghdfe} package: type {stata ssc install reghdfe, replace}"
		error 499
	}
	
	local stataversion=_caller()
	
	capt findfile hdfe.ado 
	if _rc {
		di as error "Program requires the {bf:hdfe} package: type {stata ssc install hdfe, replace}"
		error 499
	}

	marksample touse
		
	tokenize `anything'
	local subcmd `"`1'"'

	local cmdlist "m mm"
	if !`:list subcmd in cmdlist' {
		di as err `"Invalid subcommand: `subcmd'"'
		exit 
	}
		
	macro shift 1
	local depv `"`1'"'
	local varlist `"`*'"'

	// Ensure dv is not a factor variable:
	_fv_check_depvar `depv'
	macro shift 1
	local indepv "`*'"

	// Ensure dv is not an indicator variable:
	qui capture assert inlist(`depv', 0, 1)
	if _rc==0 {
        di as err "ERROR: Dependent variable should not be an indicator (0/1) variable"
        exit 		
	}	
	
	// Ensure iv list does not contain a factor variable:
    fvexpand `indepv'
    if "`r(fvops)'" == "true" {
        di as err "ERROR: Independent variable list may not contain factor variables"
        exit 
    }
	else {
		local indepv `r(varlist)'
	}
	
	// Mark out missing observations:
	markout `touse' `depv' `indepv'

	// Check for collinearity:
	_rmcoll `indepv'
	local k_omitted=r(k_omitted)
	
	// Check number of independent variables:
	local varcount=0
	foreach v of local indepv {
		local `varcount++'
	}
	scalar k0 = `varcount'
	
	// Check absorb variables:
	if "`ivar'"=="`tvar'" {
	    di as err "ERROR: Options ivar() and tvar() must contain different variables"
		exit				
	}
	capture bysort `ivar': assert `tvar'==`tvar'[1] if !missing(`ivar', `tvar')
	if _rc==0 {
	    di as err "ERROR: ivar()-variable is nested within tvar()-variable "
		exit				
	}
	capture bysort `tvar': assert `ivar'==`ivar'[1] if !missing(`tvar', `ivar')
	if _rc==0 {
	    di as err "ERROR: tvar()-variable is nested within ivar()-variable "
		exit				
	}	
	local n1: word count `ivar'
	if (`n1'!=1){
	    di as err "ERROR: Option ivar() may contain only one variable"
		exit		
	}
	local n2: word count `tvar'
	if (`n2'!=1){
	    di as err "ERROR: Option tvar() may contain only one variable"
		exit		
	}
	
	// Check nesting of FE in clusters:
	if "`cluster'"=="" {
		local nocluster=1
		local nest1=1
		local nest2=1
	}
	else {
		capture bysort `ivar': assert `cluster'==`cluster'[1] if !missing(`ivar', `cluster')
		local nest1=(_rc!=0)
		capture bysort `tvar': assert `cluster'==`cluster'[1] if !missing(`tvar', `cluster')
		local nest2=(_rc!=0)		
	}
	if (`nest2'==1) {
		local nest1dof = 0
	}
	else {
		local nest1dof = `nest1'
	}
	local nest2dof = `nest2'

	// Convert absorb variables to values available in touse:
	tempvar ivarid tvarid
	qui egen double `ivarid'=group(`ivar') if `touse'
	qui egen double `tvarid'=group(`tvar') if `touse'
		
	// Store info on estimated vs redundant parameters:	
	qui sum `ivarid'
	local ni=r(max)
	qui sum `tvarid'
	local nt=r(max)
	local ni_red = (1-`nest1')*`ni' + `nest1dof'
	local nt_red = (1-`nest2')*`nt' + `nest2dof'
	local ni_est = `ni' - (1-`nest1')*`ni' - `nest1dof'
	local nt_est = `nt' - (1-`nest2')*`nt' - `nest2dof'
	
	// Set tolerance:
	if (`tol'!=0){
		local tolerance=`tol'
	}
	else {
		local tolerance=1e-10
	}	

	// Check efficiency:
	
	if (`eff'<63.7 | `eff'>99.9) {
		di as err "ERROR: Normal efficiency must be between 63.7 and 99.9"
		exit
	}
	
	local nc: word count `cluster'
	if (`nc'>=2){
	    di as err "ERROR: Maximum number of dimensions to cluster on is one"
		exit
	}
	local clusterdim1: word 1 of `cluster'
	local clusterdim2: word 2 of `cluster'
	
	// Create temporary variables: 
	tempvar clus1  
	qui egen double `clus1'=group(`clusterdim1') if `touse'
		
	di ""
    /////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////
	di as text "STEP 1: Estimating initial MM-QR and obtaining scale estimate"
    /////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////

	// Location stage MM-QR (Machado and Santos Silva 2019)
	tempvar e Ipos r_raw denom u resid_tau
	qui capture reghdfe `depv' `indepv' if `touse', absorb(`ivarid' `tvarid') dof(none) notable nofootnote noheader resid keepsin
	qui predict double `e' if `touse', res
	qui replace `e'=0 if abs(`e')<1e-10 
	drop _reghdfe_resid

	// Scale stage
	qui gen `Ipos' = (`e'>=0) if `touse'
	qui sum `Ipos' if `touse', meanonly
	scalar Ibar = r(mean)
	qui gen double `r_raw' = 2*`e'*(`Ipos' - Ibar) if `touse'

	qui capture reghdfe `r_raw' `indepv' if `touse', absorb(`ivarid' `tvarid') dof(none) notable nofootnote noheader resid keepsin
	qui predict double `denom' if `touse', xbd
	
	// Standardized residuals and create qhat 
	qui gen double `u' = `e'/`denom' if `touse'
	qui sum `u' if `touse', d // Note: xtqreg and mmqreg use qreg on constant; I use percentile approach instead for consistency with robreg and Mata function mm_aqreg()
	scalar qhat = r(p50)

	// Residuals:
	qui gen double `resid_tau' = `e' - qhat*`denom' if `touse'
	
	// Get relevant information from the data before creating scale estimate:
	qui sum `depv' if `touse'
    local N=r(N)
	local Kinit: word count `indepv' 
	local Kinit = `Kinit' - `k_omitted'
    scalar df_initial=`N'-`ni'-`nt'-(`Kinit'-1)
	local K = `Kinit' - `k_omitted' + 1 + `ni_est' + `nt_est'

	// Get scale estimate and initial weights:
	tempvar w 
	scalar eff=`eff'
	mata: _scale_initial()

    /////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////
	di as text "STEP 2: Iterating IRWLS"
    /////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////
	tempvar _resid_temp phi
	qui gen double `phi'=.
    local diff=100
	local maxiter=c(maxiter)
    forvalues i=1(1)`maxiter'{
        if `diff'>`tolerance' {
			qui capture drop `_resid_temp'
			if (`stataversion'<19) {
				qui capture reghdfe `depv' `indepv' [aw = `w'] if `touse', absorb(`ivarid' `tvarid') dof(none) notable nofootnote noheader resid keepsin
				qui ren _reghdfe_resid `_resid_temp' 
			}
			else {
				qui capture areg `depv' `indepv' [aw = `w'] if `touse', absorb(`ivarid' `tvarid') noabs 
				qui predict `_resid_temp', res 
			}
			matrix b=e(b)            
            if `i'>1 {
                local diff=mreldif(b0,b)
            }
            matrix b0=b
			if (`i'==`maxiter' & `diff'>`tolerance'){
				di as err "ERROR: Convergence not achieved"
				exit
			}
			if (`diff'>`tolerance'){
				qui gen double _z_temp=`_resid_temp'/scale
				mata: _update_weights()
				drop _z_temp
			}
        }
    }

	if ("`weightvar'"!="") {
		capture drop `weightvar'
		if _rc==0 {
			local replaceweightvar "yes"
		}
		gen double `weightvar' = `w' 
	}
	
	qui replace `phi'=1e-20 if `phi'==0 // Ensure that residualized values are also created for phi=0 cases
	qui hdfe `indepv' if `touse' [aw = `phi'], absorb(`ivarid' `tvarid') gen(_stub_) keepsin
	local indepvr ""
	foreach v of local indepv {
		tempvar _tilde_`v'
		qui gen `_tilde_`v''=_stub_`v'
		drop _stub_`v'
		local indepvr "`indepvr' `_tilde_`v''"
	}

	// For calculation of Pseudo R2:
	scalar maxiter=`maxiter'
	mata: _huber_location()
	
	mata: ""
    /////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////
	di as text "STEP 3: Computing standard errors"
    /////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////////////////////////////////////////////////////////////

	sort `clus1' 
	local cvar "`clus1'"	
	mata: _vce_cluster()    
	local nclusterdim1=mata_nclusters
	if "`cluster'"=="" {
		local e_df_r=df_initial
	}
	else {
		local e_df_r=mata_nclusters-1
	}
	matrix beta=b0[.,1..k0]
	matrix Vc=Vclust

	if "`cluster'"=="" {
		local factor=(`N'/`e_df_r')
	}
	else{
		local factor=(`nclusterdim1'/(`nclusterdim1'-1))*((`N'-1)/(`N'-`K'))
	}
	matrix Vc=`factor'*Vc
	
	ereturn clear
	tempname b V

	matrix colnames Vc=`indepv'
	matrix rownames Vc=`indepv'
    matrix colnames beta=`indepv'	
	
	matrix `b'=beta
	matrix `V'=Vc
	
	ereturn post `b' `V'
	ereturn scalar df_r=`e_df_r'
	ereturn scalar N=`N'
	ereturn scalar r2_p=r2_p
	if "`cluster'"!="" {
		ereturn scalar N_clust=`nclusterdim1'
	}
	ereturn scalar scale=scale 
	
	di ""
	di in green "Huber M-estimation with `eff'% normal efficiency and twoway fixed effects by " ///
		in yellow "`ivar'" in green " and " in yellow "`tvar'"
	di ""
	di _column(51) in green "Number of obs = " %12.0fc in yellow e(N)
	di _column(51) in green "Pseudo R2" _column(65) "= " %12.4f in yellow e(r2_p)
	
    ereturn display
    
	if "`cluster'"!="" {
		di "SE clustered by " `nclusterdim1' " clusters in " in yellow "`clusterdim1'" 
	}
	
	if "`weightvar'"!="" {
		di in green "Robust weights stored in " in yellow "`weightvar'" 	
	}
	
	if "`replaceweightvar'"!="" {
		di in green "Careful: " in yellow "`weightvar'" in green " already existed and now replaced with new data"
	}

	local offset1 = 28 - strlen("`ni'")
	local offset2 = 28 - strlen("`nt'")
	local offset3 = 40 - strlen("`ni_red'")
	local offset4 = 40 - strlen("`nt_red'")
	local offset5 = 52 - strlen("`ni_est'")
	local offset6 = 52 - strlen("`nt_est'")
	if (`nest1'==0) {
		local star1 = "*"
	}
	else {
		local star1 = " "		
	}
	if (`nest2'==0) {
		local star2 = "*"
	}
	else {
		local star2 = " "		
	}
	
	di ""
	di in green "Degrees of freedom used by FE:"
	di "{hline 17}{c TT}{hline 36}{c TRC}"
	di "FE dimension: {col 18}{c |}  Categories - Redundant: {col 55}{c |}"
	di "{hline 17}{c +}{hline 36}{c RT}"
	di in green "`ivar' {col 17} {c |}" _column(`offset1') " `ni'" "   - " _column(`offset3') (1-`nest1')*`ni' + `nest1dof' "   = " _column(`offset5') in yellow `ni' - (1-`nest1')*`ni' - `nest1dof' " `star1' {col 53}{c |}"
	di in green "`tvar' {col 17} {c |}" _column(`offset2') " `nt'" "   - " _column(`offset4') (1-`nest2')*`nt' + `nest2dof' "   = " _column(`offset6') in yellow `nt' - (1-`nest2')*`nt' - `nest2dof' " `star2' {col 53}{c |}"
	di "{hline 17}{c BT}{hline 36}{c BRC}"
	if (`nest1'==0 | `nest2'==0) {
		di in green "* FE nested within cluster; treated as redundant for DoF calculation"
	}
	
	matrix drop beta Vc Vclust b b0
	scalar drop df_initial eff mata_nclusters scale krob
	
end

/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
// Mata programs
/////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////

mata:
	mata clear
	void _vce_cluster() {
		st_view(y=., ., st_local("depv"), st_local("touse"))
		st_view(Xr=., ., tokens(st_local("indepvr")), st_local("touse"))
		st_view(r=., ., tokens(st_local("_resid_temp")), st_local("touse"))
		st_view(cvar=., ., tokens(st_local("cvar")), st_local("touse"))
		scale=st_numscalar("scale")		
		krob=st_numscalar("krob")
		mu=st_numscalar("mu")
		nocluster=st_local("nocluster")
		
		// Process input:
		k=cols(Xr)
		z=r:/scale
		psi=mm_huber_psi(z,krob)
		phi=mm_huber_phi(z,krob)			
		
		// Compute VCE:
		XphiXinv=invsym(quadcross(Xr,phi,Xr))
		info=panelsetup(cvar, 1)
        nc=rows(info)
        M=J(k,k,0)
		if (nocluster=="") { // Loop over clusters:
			for(i=1; i<=nc; i++) {
				xi=panelsubmatrix(Xr,i,info)
				psii=panelsubmatrix(psi,i,info)
				M=M+(xi'*psii)*(psii'*xi) 
			}			
		}
		else { //Else use heteroskedasticity-robust version:
			psi2=psi:*psi
			M=quadcross(Xr,psi2,Xr)
			nc=rows(y)
		}
		
		// Combine:
		Vclust=makesymmetric(scale^2*XphiXinv*M*XphiXinv)
		
		// Export to Stata:
		st_matrix("Vclust",Vclust)
		st_numscalar("mata_nclusters",nc)

		// Compute pseudo-R2:
		z0=(y:-mu):/scale
		rho=mm_huber_rho(z,krob)			
		rho0=mm_huber_rho(z0, krob)
		r2_p=1-(colsum(rho)/colsum(rho0))
		st_numscalar("r2_p", r2_p)
	}
	    
	void _scale_initial() {
        st_view(e=., ., tokens(st_local("resid_tau")), st_local("touse"))
        df=st_numscalar("df_initial")
		eff=st_numscalar("eff")
        n=rows(e)		
        p = (2*n - df) / (2*n) 
        scale=mm_quantile(abs(e), 1, p) / invnormal(0.75) // For consistency with robreg
        z = e / scale
		krob=mm_huber_k(eff)
		w=mm_huber_w(z, krob)
		st_store(., st_addvar("double", st_local("w")), st_local("touse"), w)
        st_numscalar("scale", scale)
		st_numscalar("krob", krob)
	}
	
	void _update_weights() {
        z = st_data(., "_z_temp")
		eff=st_numscalar("eff")
		krob=mm_huber_k(eff)
		phi=mm_huber_phi(z,krob)			
		w=mm_huber_w(z, krob)
        st_store(., st_local("w"), w)
        st_store(., st_local("phi"), phi)
        printf(".")
    }

	void _huber_location() {
		st_view(y=., ., tokens(st_local("depv")), st_local("touse"))
		eff=st_numscalar("eff")
		maxiter=st_numscalar("maxiter")
		k=mm_huber_k(eff)
		mu=mm_median(y)
        scale=mm_median(abs(y :- mu)) / invnormal(0.75)
		for (i=1; i<=maxiter; i++) {
			u=(y:-mu):/scale
			w=mm_huber_w(u, k)
			mu_new=sum(w:*y) /sum(w)
			if (abs(mu_new-mu)<1e-10) break
			mu=mu_new
		}
		st_numscalar("mu", mu)
	}
	
end
	
	
	
