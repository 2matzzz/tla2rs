---- MODULE RecManyVars ----
\* A recursive operator that assigns variables in a spec with more than 64 variables
EXTENDS Naturals
VARIABLES v00, v01, v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32,
          v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65
RECURSIVE Climb(_)
\* Assigns v00 once the recursion reaches 3, from where v01 starts
Climb(k) == IF k >= 3 THEN v00' = k ELSE Climb(k + 1)
Init == /\ v00 = 0 /\ v01 = 0 /\ v02 = 0 /\ v03 = 0 /\ v04 = 0 /\ v05 = 0 /\ v06 = 0 /\ v07 = 0 /\ v08 = 0 /\ v09 = 0 /\ v10 = 0 /\ v11 = 0 /\ v12 = 0 /\ v13 = 0 /\ v14 = 0 /\ v15 = 0 /\ v16 = 0 /\ v17 = 0 /\ v18 = 0 /\ v19 = 0 /\ v20 = 0 /\ v21 = 0 /\ v22 = 0 /\ v23 = 0 /\ v24 = 0 /\ v25 = 0 /\ v26 = 0 /\ v27 = 0 /\ v28 = 0 /\ v29 = 0 /\ v30 = 0 /\ v31 = 0 /\ v32 = 0
        /\ v33 = 0 /\ v34 = 0 /\ v35 = 0 /\ v36 = 0 /\ v37 = 0 /\ v38 = 0 /\ v39 = 0 /\ v40 = 0 /\ v41 = 0 /\ v42 = 0 /\ v43 = 0 /\ v44 = 0 /\ v45 = 0 /\ v46 = 0 /\ v47 = 0 /\ v48 = 0 /\ v49 = 0 /\ v50 = 0 /\ v51 = 0 /\ v52 = 0 /\ v53 = 0 /\ v54 = 0 /\ v55 = 0 /\ v56 = 0 /\ v57 = 0 /\ v58 = 0 /\ v59 = 0 /\ v60 = 0 /\ v61 = 0 /\ v62 = 0 /\ v63 = 0 /\ v64 = 0 /\ v65 = 0
Next == /\ v01 < 4
        /\ v01' = v01 + 1
        /\ Climb(v01)
        /\ UNCHANGED <<v02, v03, v04, v05, v06, v07, v08, v09, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32,
                       v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65>>
Low == v00 < 4
====
