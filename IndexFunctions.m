(* ::Package:: *)

BeginPackage["IndexFunctions`"]

(* define functions to export *)

PochSymb::usage="q-Pochammer symbol";
eps::usage="eps(m) in summation";
nestedSum::usage="sum over n variables";
CancelTermsInSeries::usage="cancel terms in a polynomial form";
nestedCoefficient::usage="perform Contour integration using Coefficient of zero power, but assuming the expression is a polynomial (a case specific simplification algorithm is implemented)";
ImposeSUcondition::usage="impose relations between z's and m's for SU";
DefineAssumptions::usage="Assume all variables positive for symbolic manipulation";
GenerateCombinationsList::usage="Generates list of d-dimensional combinations of all integers between -intMax to intMax";
filterFluxForm::usage="filter flux combinations that have several specific forms";
ReduceCombinationsList::usage="identify equialvent flux combinations";

IndexChiral::usage="Index of U(1) N=2 chiral superfield";
IndexChiralPE::usage="Index of U(1) N=2 chiral superfield. Using the Plethystic exponent approach";
IndexChiralVec::usage="Index of U(1) N=2 chiral originating from N=4 vector superfield";
IndexChiralVecAdjSU2::usage="Index of adjoint SU(2) N=2 chiral originating from N=4 vector multiplet";
IndexHyperU1::usage="Index of U(1) N=4 hyper-multiplet";
IndexHyperU1PE::usage="Index of U(1) N=4 hyper-multiplet. Using the Plethystic exponent approach";
IndexHyperAdjSU2::usage="Index of adjoint SU(2) N=4 hyper-multiplet";
IndexVectorAdjSU2::usage="Contribution from adjoint SU(2) N=2 vector to the integrand of the gauge theory index";

IndexBifundHyper::usage="Index of bifundamental hyper for TSU(N)";
IndexChiralVecAdjUk::usage="contribution of chiral in vector for adjoint U(k)";
IndexChiralVecAdjSUk::usage="contribution of chiral in vector for adjoint SU(k)";
IndexChiralAdjUk::usage="contribution of normal chiral for adjoint U(k)";
IndexChiralAdjSUk::usage="contribution of normal chiral for adjoint SU(k)";
IndexVectorAdjUk::usage="vector contribution when gauging a non-abelian SU(k) or U(k) symmetry";
IndexHyperAdjSUN::usage="Index of adjoint SU(N) hyper, with additional fugacity a";

IndexTSU2::usage="Index of TSU(2) theory";
IndexTSU3::usage="Index of TSU(3) theory";
IntegrandTSU3::usage="Integand of Index of TSU(2) theory";
IndexTSU4::usage="Index of TSU(4) theory";
IntegrandTSU4::usage="Integand of Index of TSU(4) theory";
IndexTSUN::usage="Index of TSU(N) theory";
IntegrandTSUNlevelk::usage="Integrand of TSU(N) theory index (level k)";
IntegrateGaugeGroupTSUN::usage="Integrate integrand of TSU(N) theory index (level k)";
RecursiveIndexTSUN::usage="Internal TSU(N) function";
(*nestedSumGaugeIntegrationTSUN::usage="participates in the recursing sum and integration of TSU(N)";*)

IntegrandSSQ::usage="Integrand of SSQ index";
ExpandIntegrandSSQ::usage="Taylor expansion of integrand of SSQ index";
ResidueIndexSSQ::usage="Residue of Taylor expansion of integrand of SSQ index";
IndexSSQ::usage="Index of SSQ theory (s,g parameters)";
ExpandIndexSSQ::usage="Taylor expansion of SSQ index";

IndexSSQ3::usage="Index of SSQ3 theory (s,g parameters)";
IntegrandIndexSSQ3::usage="Integrand for SSQ3 index";
IntegrateIntegrandSSQ3::usage="Gauge integrating the Integrand for SSQ3 index";

AdjHypersSSQ::usage="Integrand of SSQ(N) index: Adj hypers";
LegsTSUN::usage="Integrand of SSQ(N) index: TSU(N) legs";
IntegrandSSQN::usage="Integrand of SSQ(N) index: full";
IndexSSQN::usage="Index of SSQ(N) theory (s,g,N parameters)";
calcTSUNbank::usage="generate bank of T[SU(N)] indices for efficiency";


Begin["`Private`"]


(* ::Subsection:: *)
(*Auxillary functions*)


Options[PochSymb]={qMax->1};
PochSymb[z_,q_,OptionsPattern[]]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(l = 0\), \(OptionValue[qMax]\)]\((1 - z*
\*SuperscriptBox[\(q\), \(l\)])\)\);


eps[m_]:=(1-(-1)^(2m))/4;


nestedSum[I_,sumVars_,numVars_,level_,mMax_]:=Module[{sumVar},
If[level==numVars+1,
I,
sumVar=sumVars[[level]];
\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(sumVar = \(-mMax\)\), \(mMax\)]\(nestedSum[I, sumVars, numVars, level + 1, mMax]\)\)
]
];


nestedCoefficient[I_,z_,k_,level_]:=Module[
{IpartiallyIntegrated,Isimplified},
If[level==k+1,
I,
(* IpartiallyIntegrated=Coefficient[I,z[[k]][[level]],0]; *)

(*Print["Simplyfing inside nestedCoefficient..."];*)
(*Isimplified=I//Simplify;*)
Isimplified=CancelTermsInSeries[I];
IpartiallyIntegrated=Coefficient[Isimplified,z[[k]][[level]],0];

nestedCoefficient[IpartiallyIntegrated,z,k,level+1]
]
];


ImposeSUcondition[z_,m_,N_]:={z[[N]][[N]]->\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(N - 1\)]
\*FractionBox[\(1\), \(\(z[\([N]\)]\)[\([j]\)]\)]\),m[[N]][[N]]->-\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(j = 1\), \(N - 1\)]\(\(m[\([N]\)]\)[\([j]\)]\)\)}


DefineAssumptions[q_,t_,a_,z_]:=Module[
{assumptions,maxVarNum},
assumptions={q>0,t>0}; (* extremely important *)
maxVarNum=Length[a];
assumptions=Join[assumptions,Table[a[[i]]>0,{i,1,maxVarNum}]];
Table[
assumptions=Join[assumptions,Table[z[[i]][[j]]>0,{j,1,maxVarNum}]]
,{i,1,maxVarNum}];
assumptions
]


VariableList[q_,t_,a_,z_,b_]:=Module[
{variableList},
variableList={1,q,t};
variableList=Join[variableList,a//Flatten];
variableList=Join[variableList,z//Flatten];
variableList=Join[variableList,b//Flatten];
variableList
]


CancelTermsInSeries[index_]:=Module[
{indexExpand,indexTerms,indexTermsSimplified,indexTermCurr,exponents,overallFactor,indexSimplified,varList,dummy},
(* dummy helps to treat the case where the series contains only a single term *)
varList=index//Variables; (*return all the variables the index depends on*) 
indexExpand=(index+dummy)//ExpandAll;
indexTerms=List@@indexExpand;
indexTerms=DeleteCases[indexTerms,dummy];
indexTermsSimplified=Table[
	indexTermCurr=indexTerms[[j]];
	exponents=Table[Exponent[indexTermCurr,varList[[i]]],{i,1,Length[varList]}];
	overallFactor=FactorTermsList[indexTermCurr][[1]];
	overallFactor \!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(Length[varList]\)]
\*SuperscriptBox[\(varList[\([i]\)]\), \(exponents[\([i]\)]\)]\)
,{j,1,Length[indexTerms]}];
indexSimplified=indexTermsSimplified//Total
]


GenerateCombinationsList[dim_,intMax_]:=Module[
{dummy,k,tableIndices,highDimTableDef,highDimTable,combinations},
tableIndices=Table[Subscript[dummy,k],{k,1,dim}];
highDimTableDef=Table[{tableIndices[[k]],-intMax,intMax},{k,1,dim}];
highDimTableDef=Join[{tableIndices},highDimTableDef];
highDimTable=Apply[Table,highDimTableDef];
combinations=Flatten[highDimTable,dim-1];
combinations
]


filterFluxForm[m_,k_,N_]:=
Module[{validFlux,mNoZeros,condition},
validFlux=True;
(*If[k==N-1 && k!=1,*)
(*Print["m=", m, ", k=", k,", N=", N];*)
If[True,
	mNoZeros=DeleteCases[m,0];
	validFlux = Which[
					Length[mNoZeros]==0, 
						True,
					Length[mNoZeros]==1,
						If[Abs[Total[mNoZeros]]<=2,True,False],
					Length[mNoZeros]==2,
						If[k==N-1,
							condition = ( Abs[Total[mNoZeros]]==0 && Total[Abs[mNoZeros]]==2 );
							(*condition = ( Abs[Total[mNoZeros]]\[Equal]2 && Total[Abs[mNoZeros]]\[Equal]2 ) || ( Abs[Total[mNoZeros]]==0 && Total[Abs[mNoZeros]]==2 );	*)						
						,	
							(*condition = ( Abs[Total[mNoZeros]]==1 && Total[Abs[mNoZeros]]==3 ) || ( Abs[Total[mNoZeros]]==0 && Total[Abs[mNoZeros]]==2 ); *)
							(* condition = True; *)
							condition = ( Abs[Total[mNoZeros]]==2 && Total[Abs[mNoZeros]]==2 ) || ( Abs[Total[mNoZeros]]==1 && Total[Abs[mNoZeros]]==3 ) || ( Abs[Total[mNoZeros]]==0 && Total[Abs[mNoZeros]]==2 );
						];
						If[condition, True, False],
					True,
						False
					];
];	
validFlux
]


ReduceCombinationsList[mCombinations_,k_,N_]:=
Module[{i,doNotFilterAtAll,combosEquivalent,combosEquivalentMultiplicities,currCombo,currComboStandardForm,
currComboMinusStandardForm,indexEquivalentCombo,filterByForm,identifyOppositeSigns},
combosEquivalent={};
combosEquivalentMultiplicities={};
For[i=1,i<=Length[mCombinations],i++,
	(* transform combonation to a standard form by sorting *)
	currCombo=mCombinations[[i]];
	currComboStandardForm=Sort[currCombo,Greater];
	currComboMinusStandardForm=Sort[-currCombo,Greater];

	(* check if already exists in the list of equivalent combinations *)
	indexEquivalentCombo=Position[combosEquivalent,currComboStandardForm];
	
	(* identify combinations that differ by sign only *)
	identifyOppositeSigns=False;
	If[identifyOppositeSigns && k==N-1,
		indexEquivalentCombo=Join[Position[combosEquivalent,currComboStandardForm],Position[combosEquivalent,currComboMinusStandardForm]];
	];

	(* filter only combinations of specific form *)
	filterByForm=True;
	If[filterByForm && (filterFluxForm[currCombo,k,N]==False),
		Continue[]
	];
	
	(* update the equivalent combimations bank *)
	If[Length[indexEquivalentCombo]==0,
		combosEquivalent=Join[combosEquivalent,{currComboStandardForm}];
		combosEquivalentMultiplicities=Join[combosEquivalentMultiplicities,{1}];
	,
		combosEquivalentMultiplicities[[indexEquivalentCombo[[1]]]]=combosEquivalentMultiplicities[[indexEquivalentCombo[[1]]]]+1;
	];
];

(* option to not filter any combination *)
doNotFilterAtAll=False;
If[doNotFilterAtAll, 
	combosEquivalent=mCombinations;
	combosEquivalentMultiplicities=Table[1,{i,1,Length[mCombinations]}];
];
	
{combosEquivalent,combosEquivalentMultiplicities}
]


(* ::Subsection:: *)
(*Indices of N=4 building blocks*)


(* N=2 chiral *)
(*IndexChiral[q_,t_,z_,m_]:=(q^(1/2)/t)^(Abs[m]/4)PochSymb[t^(-1/2) q^(3/4+Abs[m]/2) z,q]/PochSymb[t^(+1/2) q^(1/4+Abs[m]/2) z,q];*)
IndexChiral[q_,t_,z_,m_]:=(q^(1/4)/(z t^(1/2)))^(Abs[m]/2)PochSymb[ q^(3/4+Abs[m]/2)(-1)^(-m) z^(-1) t^(-1/2),q]/
	PochSymb[q^(1/4+Abs[m]/2)(-1)^m z t^(+1/2),q];	


Options[IndexChiralPE]={PEpower->4};
IndexChiralPE[q_,z_,r_,m_,OptionsPattern[]]:=(q^((1-r)/2)/z)^(Abs[m]/2) Exp[\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(k = 1\), \(OptionValue[PEpower]\)]\((
\*FractionBox[\(1\), \(k\)] \((
\*SuperscriptBox[\((
\*SuperscriptBox[\(q\), \(
\*FractionBox[\(r\), \(2\)] + 
\*FractionBox[\(Abs[m]\), \(2\)]\)] 
\*SuperscriptBox[\((\(-1\))\), \(m\)] z)\), \(k\)] - 
\*SuperscriptBox[\((
\*SuperscriptBox[\(q\), \(
\*FractionBox[\(2 - r\), \(2\)] + 
\*FractionBox[\(Abs[m]\), \(2\)]\)] 
\*SuperscriptBox[\((\(-1\))\), \(-m\)] 
\*SuperscriptBox[\(z\), \(-1\)])\), \(k\)])\) \(
\*UnderoverscriptBox[\(\[Sum]\), \(l = 0\), \(1\)]
\*SuperscriptBox[\(q\), \(k\ l\)]\))\)\)];	


(* N=2 chiral that originated from N=4 vector (different t,q powers) *)
(* IndexChiralVec[q_,t_,z_,m_] :=(q^(1/2)/t)^(-Abs[m]/2)PochSymb[t q^(1/2+Abs[m]/2) z,q]/PochSymb[t^-1 q^(1/2+Abs[m]/2) z,q]; *)
(*IndexChiralVec[q_,t_,z_,m_]:=(1/(z t^(-1)))^(Abs[m]/2)PochSymb[ q^(1/2+Abs[m]/2)(-1)^(-m) z^(-1) t,q]/PochSymb[q^(1/2+Abs[m]/2)(-1)^m z t^-1 ,q];*)
IndexChiralVec[q_,t_,z_,m_]:=(z/t)^(-Abs[m]/2)PochSymb[ q^(1/2+Abs[m]/2)(-1)^(-m) z^(-1) t,q]/PochSymb[q^(1/2+Abs[m]/2)(-1)^m z t^-1 ,q];


IndexChiralVecAdjSU2[q_,t_,z_,m_]:=IndexChiralVec[q,t,1,0]IndexChiralVec[q,t,z^2,2m]IndexChiralVec[q,t,z^-2,-2m]


(* N=4 hyper composed of 2 chirals, here with U(1) opposite charges*)
IndexHyperU1[q_,t_,z_,m_]:=IndexChiral[q,t,z,m]IndexChiral[q,t,z^-1,-m]


IndexHyperU1PE[q_,t_,z_,m_]:=IndexChiralPE[q,z t^(1/2),1/2,m]IndexChiralPE[q,z^-1 t^(1/2),1/2,m]


(* Index of adjoint SU(2) hyper, with additional fugacity a *)
IndexHyperAdjSU2[q_,t_,z_,m_,a_]:=IndexHyperU1[q,t,a,0]IndexHyperU1[q,t,z^2 a,2m]IndexHyperU1[q,t,z^-2 a,-2m]


(* N=4 vectors contribute when gauging a non-abelian symmetry *) (* TO DELETE, NOT USED EQUATIONS, WITHOUT THE CORRECT FACTORS *)
IndexVectorAdjSU2[q_,z_,m_]:=(1-q^Abs[m] z^2)(1-q^Abs[m] z^-2);


(* bifundamental hyper of groups U(k) and U(k+1), except for k=N-1, where it is U(N-1) and SU(N) *)
IndexBifundHyper[q_,t_,z_,m_,k_,N_]:=Module[{index},
If[k>N-1,Print["error k>N-1"],
index=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(k + 1\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(k\)]IndexHyperU1[q, t, \(z[\([k]\)]\)[\([i]\)]/\(z[\([k + 1]\)]\)[\([j]\)], \(m[\([k]\)]\)[\([i]\)] - \(m[\([k + 1]\)]\)[\([j]\)]])\)\);
If[k==N-1,
index=index/.ImposeSUcondition[z,m,k+1]];
index
]];


(* contribution of chiral in vector for adjoint U(k) *)
IndexChiralVecAdjUk[q_,t_,z_,m_,k_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(k\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(k\)]IndexChiralVec[q, t, 
\*FractionBox[\(\(z[\([k]\)]\)[\([i]\)]\), \(\(z[\([k]\)]\)[\([j]\)]\)], \(m[\([k]\)]\)[\([i]\)] - \(m[\([k]\)]\)[\([j]\)]])\)\);


(* contribution of normal chiral for adjoint U(k) *)
IndexChiralAdjUk[q_,t_,z_,m_,k_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(k\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(k\)]IndexChiral[q, t, 
\*FractionBox[\(\(z[\([k]\)]\)[\([i]\)]\), \(\(z[\([k]\)]\)[\([j]\)]\)], \(m[\([k]\)]\)[\([i]\)] - \(m[\([k]\)]\)[\([j]\)]])\)\);


(* contribution of chiral in vector for adjoint SU(k) *)
IndexChiralVecAdjSUk[q_,t_,z_,m_,k_]:=IndexChiralVecAdjUk[q,t,z,m,k]/IndexChiralVec[q,t,1,0]/.ImposeSUcondition[z,m,k];


(* contribution of normal chiral for adjoint SU(k) *)
IndexChiralAdjSUk[q_,t_,z_,m_,k_]:=IndexChiralAdjUk[q,t,z,m,k]/IndexChiral[q,t,1,0]/.ImposeSUcondition[z,m,k];


(* vector contribution when gauging a non-abelian SU(k) or U(k) symmetry *)
(*IndexVectorAdjUk[q_,z_,m_,k_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(k\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(k\)]If[i != j, \((1 - \ 
\*FractionBox[\(\(z[\([k]\)]\)[\([i]\)]\), \(\(z[\([k]\)]\)[\([j]\)]\)]q^Abs[\((\(m[\([k]\)]\)[\([i]\)] - \(m[\([k]\)]\)[\([j]\)])\)/2])\), 1])\)\);*)
IndexVectorAdjUk[q_,z_,m_,k_]:=\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(k\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(k\)]If[i != j, q^\((\(-Abs[\((\(m[\([k]\)]\)[\([i]\)] - \(m[\([k]\)]\)[\([j]\)])\)/4]\))\) \((1 - \((\(-1\))\)^\((\(m[\([k]\)]\)[\([i]\)] - \(m[\([k]\)]\)[\([j]\)])\)\ 
\*FractionBox[\(\(z[\([k]\)]\)[\([i]\)]\), \(\(z[\([k]\)]\)[\([j]\)]\)] q^Abs[\((\(m[\([k]\)]\)[\([i]\)] - \(m[\([k]\)]\)[\([j]\)])\)/2])\), 1])\)\);


(* Index of adjoint SU(N) hyper, with additional fugacity a *)
IndexHyperAdjSUN[q_,t_,z_,m_,a_,N_]:=IndexHyperU1[q,t,a,0]^(N-1) \!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(N\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(N\)]If[i != j, IndexHyperU1[q, t, 
\*FractionBox[\(\(z[\([N]\)]\)[\([i]\)]\), \(\(z[\([N]\)]\)[\([j]\)]\)] a, \(m[\([N]\)]\)[\([i]\)] - \(m[\([N]\)]\)[\([j]\)]], 1])\)\)/.ImposeSUcondition[z,m,N];


(* ::Subsection::Closed:: *)
(*T[SU(2)] theory Index*)


(* 2 hypers SU(2) *)
IntegrandIndexTSU2[q_,t_,z_,mt_,a_,m_,n_]:=z^(2n) IndexChiralVec[q,t,1,0]IndexHyperU1[q,t,z a,mt+m]IndexHyperU1[q,t,z a^-1,mt-m]


ExpandIntegrandIndexTSU2[q_,t_,z_,mt_,a_,m_,n_,qMaxTSU2_]:=
Assuming[{z>0,a>0},
Normal[Series[IntegrandIndexTSU2[q,t,z,mt,a,m,n],{q,0,qMaxTSU2}]]//Simplify
]
(*Normal[Series[IntegrandIndexTSU2[q,t,z,mt,a,m,n],{q,0,qMaxTSU2}]];*)


ResidueIntegralIndexTSU2[q_,t_,mt_,a_,m_,n_,qMaxTSU2_]:=Module[{z},
Assuming[{z>0,a>0},
Coefficient[ExpandIntegrandIndexTSU2[q,t,z,mt,a,m,n,qMaxTSU2],z,0]
]
]
(*Coefficient[ExpandIntegrandIndexTSU2[q,t,z,mt,a,m,n,qMaxTSU2],z,0]]*)


IndexTSU2[q_,t_,a_,m_,b_,n_,qMaxTSU2_,mMaxTSU2_] := \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(mt = \(-mMaxTSU2\) + eps[m]\), \(mMaxTSU2\)]\(
\*SuperscriptBox[\(b\), \(2  mt\)] ResidueIntegralIndexTSU2[q, t, mt, a, m, n, qMaxTSU2]\)\);


(* ::Subsection::Closed:: *)
(*T[SU(3)] theory Index*)


(* T[SU(3)] Index *)
IndexTSU3[q_,t_,z_,m_,b_,n_,mMax_,qMax_]:=Series[Coefficient[Coefficient[Coefficient[Normal[Series[IntegrandTSU3[q,t,z,m,b,n,mMax,qMax],{q,0,qMax}]],z[[1]][[1]],0],z[[2]][[1]],0],z[[2]][[2]],0],{q,0,qMax}]//Normal


(*(* T[SU(3)] Index *)
IntegrandTSU3[q_,t_,z_,m_,b_,n_,mMax_,qMax_]:=Module[{mCurr},
\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(\(m[\([2]\)]\)[\([2]\)] = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(\(m[\([2]\)]\)[\([1]\)] = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(\(m[\([1]\)]\)[\([1]\)] = \(-mMax\)\), \(mMax\)]\((\n1/\(2!\)\ 1/\(3!\)\ \(b[\([1]\)]\)[\([1]\)]^\((2\(
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(1\)]\(m[\([1]\)]\)[\([i]\)]\))\)\(b[\([1]\)]\)[\([2]\)]^\((2\(
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(2\)]\(m[\([2]\)]\)[\([i]\)]\))\)IndexVectorAdjUk[q, z, m, 1]IndexChiralVecAdjUk[q, t, z, m, 1]IndexBifundHyper[q, t, z, m, 1, 3]IndexVectorAdjUk[q, z, m, 2]IndexChiralVecAdjUk[q, t, z, m, 2]IndexBifundHyper[q, t, z, m, 2, 3])\))\))\)\)
]*)


(* T[SU(3)] Index *)
IntegrandTSU3[q_,t_,z_,m_,b_,n_,mMax_,qMax_]:=Module[{mCurr},
1/1! 1/2!\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m22 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m21 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m11 = \(-mMax\)\), \(mMax\)]\((\nmCurr = m /. {\(m[\([2]\)]\)[\([2]\)] -> m22, \(m[\([2]\)]\)[\([1]\)] -> m21, \(m[\([1]\)]\)[\([1]\)] -> m11}; \n\(b[\([1]\)]\)[\([1]\)]^\((
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(1\)]\(mCurr[\([1]\)]\)[\([i]\)])\) \(b[\([1]\)]\)[\([2]\)]^\((
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(2\)]\(mCurr[\([2]\)]\)[\([i]\)])\) \((
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(1\)]\(z[\([1]\)]\)[\([i]\)])\)^\((2 \( n[\([1]\)]\)[\([1]\)])\)\ \((
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(2\)]\(z[\([2]\)]\)[\([i]\)])\)^\((2 \( n[\([1]\)]\)[\([2]\)])\)\ IndexVectorAdjUk[q, z, mCurr, 1] IndexChiralVecAdjUk[q, t, z, mCurr, 1] IndexBifundHyper[q, t, z, mCurr, 1, 3] IndexVectorAdjUk[q, z, mCurr, 2] IndexChiralVecAdjUk[q, t, z, mCurr, 2] IndexBifundHyper[q, t, z, mCurr, 2, 3])\))\))\)\)
]


(* ::Subsection::Closed:: *)
(*T[SU(4)] theory Index*)


(* T[SU(4)] Index *)
IndexTSU4[q_,t_,z_,m_,b_,n_,mMax_,qMax_]:=Series[Coefficient[Coefficient[Coefficient[Coefficient[Coefficient[Coefficient[Normal[Series[IntegrandTSU4[q,t,z,m,b,n,mMax,qMax],{q,0,qMax}]],z[[1]][[1]],0],z[[2]][[1]],0],z[[2]][[2]],0],z[[3]][[1]],0],z[[3]][[2]],0],z[[3]][[3]],0],{q,0,qMax}]//Normal


(* T[SU(4)] Index *)
IntegrandTSU4[q_,t_,z_,m_,b_,n_,mMax_,qMax_]:=Module[{mCurr},
1/1! 1/2! 1/3!\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m33 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m32 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m31 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m22 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m21 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m11 = \(-mMax\)\), \(mMax\)]\((\nmCurr = m /. {\(m[\([3]\)]\)[\([3]\)] -> m33, \(m[\([3]\)]\)[\([2]\)] -> m32, \(m[\([3]\)]\)[\([1]\)] -> m31, \(m[\([2]\)]\)[\([2]\)] -> m22, \(m[\([2]\)]\)[\([1]\)] -> m21, \(m[\([1]\)]\)[\([1]\)] -> m11}; \n\(b[\([1]\)]\)[\([1]\)]^\((
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(1\)]\(mCurr[\([1]\)]\)[\([i]\)])\) \(b[\([1]\)]\)[\([2]\)]^\((
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(2\)]\(mCurr[\([2]\)]\)[\([i]\)])\) \(b[\([1]\)]\)[\([3]\)]^\((
\*UnderoverscriptBox[\(\[Sum]\), \(i = 1\), \(3\)]\(mCurr[\([3]\)]\)[\([i]\)])\) \((
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(1\)]\(z[\([1]\)]\)[\([i]\)])\)^\((2 \( n[\([1]\)]\)[\([1]\)])\)\ \((
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(2\)]\(z[\([2]\)]\)[\([i]\)])\)^\((2 \( n[\([1]\)]\)[\([2]\)])\) \((
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(3\)]\(z[\([3]\)]\)[\([i]\)])\)^\((2 \( n[\([1]\)]\)[\([3]\)])\)\ IndexVectorAdjUk[q, z, mCurr, 1] IndexChiralVecAdjUk[q, t, z, mCurr, 1] IndexBifundHyper[q, t, z, mCurr, 1, 4] IndexVectorAdjUk[q, z, mCurr, 2] IndexChiralVecAdjUk[q, t, z, mCurr, 2] IndexBifundHyper[q, t, z, mCurr, 2, 4] IndexVectorAdjUk[q, z, mCurr, 3] IndexChiralVecAdjUk[q, t, z, mCurr, 3] IndexBifundHyper[q, t, z, mCurr, 3, 4])\))\))\))\))\))\)\)
]


(* ::Subsection:: *)
(*T[SU(N)] theory Index*)


(* T[SU(N)] Index *)
IndexTSUN[q_,t_,z_,m_,b_,n_,N_,mMax_,qMax_,verbosity_]:=
Module[{res},
(*If[verbosity==1,Print["Number of flux combinations of U(N-1) gauge group = (2mMax+1\!\(\*SuperscriptBox[\()\), \((N - 1)\)]\) = ", (2mMax[[N-1]]+1)^(N-1)]];*)
(*If[verbosity==1,Print["Number of flux combinations of U(", N-1, ") gauge group = ", \!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(N - 1\)]\((2 mMax[\([N - 1]\)] + 1)\)\)]];*)
(* start recursive function with k=N-1, the leftmost gauge group factor U(k) *)
res=Normal[Series[RecursiveIndexTSUN[q,t,z,m,N-1,b,n,N,mMax,qMax,verbosity],{q,0,qMax}]]//Timing; 
If[verbosity>=1,Print["Index T[SU(",N,")] calculation time = ", res[[1]], " seconds" ]];
res[[2]]
];


(* Recursive interior of T[SU(N)] Index function *)
RecursiveIndexTSUN[q_,t_,z_,m_,k_,b_,n_,N_,mMax_,qMax_,verbosity_]:=
Module[{Ilast,Ilevelk},
If[k==0,
	1, (* recursion goes back from k=N-1 to k=0 *)
	(*If[N<4,mMax=2]; (*testing for more efficient N=5 calc*)*)
	Ilevelk=nestedSumGaugeIntegrationTSUN[q,t,z,m,k,b,n,N,mMax,qMax,verbosity];
	(*Print["level k=",k];
	Print["Ilevelk=",Ilevelk];*)
	Ilevelk
]
];


nestedSumGaugeIntegrationTSUN[q_,t_,z_,m_,k_,b_,n_,N_,mMax_,qMax_,verbosity_]:=
Module[{i,IlevelkGauged,mCombinations,mCombinationsReduced,mCombinationsMultiplicity,fluxContributions,
mUpdated,statusStr,totalIndex,identifyOppositeSigns,bTranformationInverse,fluxPair},

mCombinations=GenerateCombinationsList[k,mMax[[k]]];
{mCombinationsReduced,mCombinationsMultiplicity}=ReduceCombinationsList[mCombinations,k,N];
(*Print["Gauge group U(", ToString[k], ") number of flux combinations = ", Length[mCombinationsReduced]];*)
If[k>=N-1,Print["Gauge group U(", ToString[k], ") number of flux combinations = ", Length[mCombinationsReduced]]];
(*If[k\[Equal]N-2,Print["Gauge group U(", ToString[k], ") number of flux combinations = ", Length[mCombinationsReduced]]];*)
If[k>=N-2,Print["Gauge group U(", ToString[k], ") flux combinations = ", {mCombinationsReduced,mCombinationsMultiplicity}]];
(*Print["mCombinationsReduced=",mCombinationsReduced];*)

fluxContributions=Table[0,{i,1,Length[mCombinationsReduced]}];
For[i=1,i<=Length[mCombinationsReduced],i++,
	(*Print["i=", i, "/Length[mCombinationsReduced]=", Length[mCombinationsReduced]];*)
	mUpdated=m;
	mUpdated[[k]][[1;;k]]=mCombinationsReduced[[i]];
	(*Print["curr fluxes = ", mCombinationsReduced\[LeftDoubleBracket]i\[RightDoubleBracket]];*)
	
	statusStr=StringJoin["Gauge group U(", ToString[k], ") fluxes m[[", ToString[k] ,"]]=", ToString[mCombinationsReduced[[i]]]];
	If[k==N-1, Print[StringJoin["debugging. pre calc of ", statusStr]] ];
	(*Print["mUpdated= ", mUpdated];	*)
	
	IlevelkGauged=IntegrateGaugeGroupTSUN[q,t,z,mUpdated,k,b,n,N,mMax,qMax,verbosity];
	fluxContributions[[i]]=mCombinationsMultiplicity[[i]] 1/k! b[[k]]^(Total[mCombinationsReduced[[i]]]) IlevelkGauged;
	(*If[k\[Equal]N-1,Print["debugging. Curr flux = ", mCombinationsReduced\[LeftDoubleBracket]i\[RightDoubleBracket], ", contribution = ", fluxContributions\[LeftDoubleBracket]i\[RightDoubleBracket]]];*)

	If[k==N-1, 
		Print["Saving flux to file."];
		(*fluxContribution=fluxContributions[[i]];*)
		fluxPair={mCombinationsReduced[[i]],fluxContributions[[i]]};
		Export[StringJoin["indices_saves/TSUN_indices/index_TSU", ToString[N], "_contributions/index_TSU", ToString[N], "_flux_index_", ToString[i], ".mx"], fluxPair] 
	];
	
	(* Print status *)	
	If[verbosity==1,
		If[k==N-1 || k==N-2,
			If[fluxContributions[[i]]===0,
				Print[ StringJoin[statusStr, ": zero contribution."] ];
			,
				Print[statusStr];
				(*Print["debugging. Gauge group U(", k, ") flux contribution = ", fluxContributions[[i]]];*)
			]
		]
	];
	
];
(*Print["Gauge group U(", ToString[k], "), fluxContributions = ", fluxContributions];*)
If[k==N-1, 
	Print["Saving all fluxes to file."];
	(*fluxContributionTable=fluxContributions;*)
	Export[StringJoin["indices_saves/TSUN_indices/index_TSU", ToString[N], "_contributions/index_TSU", ToString[N], "_all_fluxes_table.mx"],fluxContributions] 
];
	

totalIndex=Total[fluxContributions];
(*Print["totalIndex=", totalIndex];*)

(* the opposite sign fluxes are equivalent to taking the inverse of b(k) *)
identifyOppositeSigns=False;
If[identifyOppositeSigns && k==N-1,
	Print["Gauge group U(", ToString[k], ") applying b symmetrization on the total index."];
	bTranformationInverse=Table[b[[i]]->b[[i]]^-1,{i,1,Length[b]}];
	totalIndex=1/2*(totalIndex+(totalIndex/.bTranformationInverse));
];
(*Print["totalIndex=", totalIndex];*)

totalIndex
];


IntegrateGaugeGroupTSUN[q_,t_,z_,m_,k_,b_,n_,N_,mMax_,qMax_,verbosity_]:=
Module[{Ilast,ItoIntegrate,ItoIntegrateExpanded,IafterIntegration,varList,INumeratorExpanded,IDenominatorExpanded,qMaxInternal},
Ilast=RecursiveIndexTSUN[q,t,z,m,k-1,b,n,N,mMax,qMax,verbosity]; (* recursion step to level k-1 *)
(*If[k==N-1,Print["debugging. Gauge group U(", k, "), Ilast = ",  Ilast]];*)
(*Print["Ilast=",Ilast];*)
ItoIntegrate=IntegrandTSUNlevelk[q,t,z,m,k,n,N]Ilast;

(*Print["m= ", m];*)
(*If[k\[Equal]2,Print["debugging. Gauge group U(", k, "), ItoIntegrate = ",  ItoIntegrate]];*)
(*If[k==N-1,Print["debugging. Gauge group U(", k, "), before Series[]"]];*)

qMaxInternal=If[N>=5 && k<N-1, qMax+1,qMax];
(*Print["qMaxInternal=",qMaxInternal];*)
ItoIntegrateExpanded=Normal[Series[ItoIntegrate,{q,0,qMaxInternal}]];
(*If[k\[Equal]2,Print["debugging. Gauge group U(", k, "), ItoIntegrateExpanded = ",  ItoIntegrateExpanded]]; *)

(*
INumeratorExpanded=Series[ItoIntegrate//Numerator,{q,0,2*qMax}]//Normal;
IDenominatorExpanded=Series[ItoIntegrate//Denominator,{q,0,2*qMax}]//Normal;
ItoIntegrateExpanded = If[(INumeratorExpanded===0)||(IDenominatorExpanded===0),0,
	Series[INumeratorExpanded/IDenominatorExpanded,{q,0,qMax}]//Normal
	];
*)

(*Print["k=",k];
Print["ItoIntegrateExpanded=",ItoIntegrateExpanded];*)
(*varList=ItoIntegrateExpanded//Variables; (*return all the variables the index depends on*) *)
(*If[k==N-1,Print["Gauge group U(", k, "), Index before nestedCoefficient depends on the variables = ",  varList]];*)
(*If[k==N-1,Print["debugging. Gauge group U(", k, "), Index before nestedCoefficient = ",  ItoIntegrateExpanded]];*)
(*If[k==N-1,Print["debugging. made it to before before nestedCoefficient"]];*)
IafterIntegration=nestedCoefficient[ItoIntegrateExpanded,z,k,1];
(*If[k==N-1,Print["debugging. Gauge group U(", k, "), Index after nestedCoefficient = ",  IafterIntegration]];*)
(*Print["IafterIntegration=",IafterIntegration];*)
IafterIntegration
];


IntegrandTSUNlevelk[q_,t_,z_,m_,k_,n_,N_]:=(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(k\)]\(\(z[\([k]\)]\)[\([i]\)]\)\))^(2n[[k]]) IndexVectorAdjUk[q,z,m,k]IndexChiralVecAdjUk[q,t,z,m,k]IndexBifundHyper[q,t,z,m,k,N];


(* ::Subsection::Closed:: *)
(*SSQ(2) (Star Shaped Quiver with N=2) theory Index*)


IntegrandSSQ[q_,t_,n_,a_,b_,z_,s_,g_,mt_,qMaxTSU2_,mMaxTSU2_] := IndexVectorAdjSU2[q,z,mt]IndexChiralVecAdjSU2[q,t,z,mt](\!\(
\*UnderoverscriptBox[\(\[Product]\), \(l = 1\), \(g\)]\(IndexHyperAdjSU2[q, t, z, mt, a[\([l]\)]]\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(l = 1\), \(s\)]\(IndexTSU2[q, 
\*SuperscriptBox[\(t\), \(-1\)], b[\([l]\)], n[\([l]\)], z, mt, qMaxTSU2, mMaxTSU2]\)\));


ExpandIntegrandSSQ[q_,t_,n_,a_,b_,z_,s_,g_,mt_,qMaxTSU2_,mMaxTSU2_,qMaxSSQ_] := Normal[Series[IntegrandSSQ[q,t,n,a,b,z,s,g,mt,qMaxTSU2,mMaxTSU2],{q,0,qMaxSSQ}]];


ResidueIndexSSQ[q_,t_,n_,a_,b_,s_,g_,mt_,qMaxTSU2_,mMaxTSU2_,qMaxSSQ_]:=Coefficient[ExpandIntegrandSSQ[q,t,n,a,b,z,s,g,mt,qMaxTSU2,mMaxTSU2,qMaxSSQ],z,0];


IndexSSQ[q_,t_,n_,a_,b_,s_,g_,qMaxTSU2_,mMaxTSU2_,qMaxSSQ_,mMaxSSQ_,gaugeGroup_]:=(
If[gaugeGroup=="SU2",
(* for SU2 gauge group the sum is on integers mt\[Element]Z *)
1/2 \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(mt = \(-mMaxSSQ\)\), \(mMaxSSQ\)]\(ResidueIndexSSQ[q, t, n, a, b, s, g, mt, qMaxTSU2, mMaxTSU2, qMaxSSQ]\)\),
If[gaugeGroup=="SO3",
(* for SO3 gauge group the sum is on integers and half-integers mt\[Element]Z/2 *)
1/2 \!\(
\*UnderoverscriptBox[\(\[Sum]\), \(mt = \(-2\)\ mMaxSSQ\), \(2\ mMaxSSQ\)]\(ResidueIndexSSQ[q, t, n, a, b, s, g, 
\*FractionBox[\(mt\), \(2\)], qMaxTSU2, mMaxTSU2, qMaxSSQ]\)\),
Print["Gauge group invalid, only options are SU2 and SO3"];
]]
)


ExpandIndexSSQ[q_,t_,n_,a_,b_,s_,g_,qMaxTSU2_,mMaxTSU2_,qMaxSSQ_,mMaxSSQ_,gaugeGroup_]:=
Module[{IndexSSQfull},
IndexSSQfull=IndexSSQ[q,t,n,a,b,s,g,qMaxTSU2,mMaxTSU2,qMaxSSQ,mMaxSSQ,gaugeGroup]//Timing;
Print["Index calculation time = ", IndexSSQfull[[1]], " seconds" ];
Series[IndexSSQfull[[2]],{q,0,qMaxSSQ}]//ExpandAll
]


(* ::Subsection::Closed:: *)
(*SSQ(3) Index*)


IndexSSQ3[q_,t_,n_,a_,b_,z_,s_,g_,m_,qMax_,mMax_]:=Module[
{mCurr},
1/3!\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(m32 = \(-mMax\)\), \(mMax\)]\((
\*UnderoverscriptBox[\(\[Sum]\), \(m31 = \(-mMax\)\), \(mMax\)]\((\nmCurr = m /. {\(m[\([3]\)]\)[\([2]\)] -> m32, \(m[\([3]\)]\)[\([1]\)] -> m31}; \nIntegrateIntegrandSSQ3[q, t, n, a, b, z, s, g, mCurr, qMax, mMax]\n)\))\)\)
]


IntegrateIntegrandSSQ3[q_,t_,n_,a_,b_,z_,s_,g_,m_,qMax_,mMax_]:=Series[Coefficient[Coefficient[Normal[Series[IntegrandSSQ3[q,t,n,a,b,z,s,g,m,qMax,mMax],{q,0,qMax}]],z[[3]][[1]],0],z[[3]][[2]],0],{q,0,qMax}]//Normal


IntegrandSSQ3[q_,t_,n_,a_,b_,z_,s_,g_,m_,qMax_,mMax_]:=IndexVectorAdjUk[q,z,m,3]IndexChiralVecAdjSUk[q,t,z,m,3]AdjHypersSSQ[q,t,a,z,m,g,3]/.ImposeSUcondition[z,m,3]


(* ::Subsection:: *)
(*SSQ(N) Index*)


(* SSQ(N) Index *)
IndexSSQN[q_,t_,a_,b_,n_,z_,m_,s_,g_,N_,mMax_,qMax_,TSUNbank_,verbosity_]:=
Module[{res},
(*res=Series[nestedSumGaugeIntegrationSSQN[q,t,a,b,n,z,m,s,g,N,mMax,qMax,1,verbosity],{q,0,qMax}]//Timing; (* start recursive function with k=N-1 *)*)
res=nestedSumGaugeIntegrationSSQN[q,t,a,b,n,z,m,s,g,N,mMax,qMax,TSUNbank,1,verbosity]//Timing; (* start recursive function with k=N-1 *)
Print["Index SSQ(", N, ") calculation time = ", res[[1]], " seconds" ];
res[[2]]
];


nestedSumGaugeIntegrationSSQN[q_,t_,a_,b_,n_,z_,m_,s_,g_,N_,mMax_,qMax_,TSUNbank_,level_,verbosity_]:=
Module[{IlevelkGauged,mSummedCurr,mMaxCurr,sumElement,sumTotal},
If[level==N, 
	(* at this point, all m[[N]] sum variables are numerically defined *)
	(*Print["m[[N]]=",m[[N]]];*)
	sumElement=1/N!IntegrateGaugeGroupSSQN[q,t,a,b,n,z,m,s,g,N,mMax,qMax,TSUNbank];
	sumElement
,
	(* multi-variable sum using recursion *)
	mSummedCurr=m[[N]][[level]];
	mMaxCurr=mMax[[N]]; 
	(*If[verbosity==1,Print["mSummed=",mSummed]];*)
	sumTotal=\!\(
\*UnderoverscriptBox[\(\[Sum]\), \(mCurr = \(-mMaxCurr\)\), \(mMaxCurr\)]\(nestedSumElementSSQN[q, t, a, b, n, z, m, mSummedCurr, mCurr, s, g, N, mMax, qMax, TSUNbank, level + 1, verbosity]\)\);
	sumTotal
]
];


nestedSumElementSSQN[q_,t_,a_,b_,n_,z_,m_,mSummed_,mCurr_,s_,g_,N_,mMax_,qMax_,TSUNbank_,level_,verbosity_]:=(
(* If[verbosity==1,Print[mSummed,"=",mCurr]]; *)
If[verbosity==1,Print["m=",m[[N]][[;;N-1]]/.{mSummed->mCurr}]];
nestedSumGaugeIntegrationSSQN[q,t,a,b,n,z,m/.{mSummed->mCurr},s,g,N,mMax,qMax,TSUNbank,level,verbosity]
);


IntegrateGaugeGroupSSQN[q_,t_,a_,b_,n_,z_,m_,s_,g_,N_,mMax_,qMax_,TSUNbank_]:=
Module[{ItoIntegrate,ItoIntegrateExpanded,IafterIntegration},
ItoIntegrate=IntegrandSSQN[q,t,a,b,n,z,m,s,g,N,mMax,qMax,TSUNbank];
ItoIntegrateExpanded=Normal[Series[ItoIntegrate,{q,0,qMax}]];
IafterIntegration=nestedCoefficient[ItoIntegrateExpanded,z,N,1];
IafterIntegration
];


IntegrandSSQN[q_,t_,a_,b_,n_,z_,m_,s_,g_,N_,mMax_,qMax_,TSUNbank_]:=
Module[{adjHypers,legs,integrand},
adjHypers=AdjHypersSSQ[q,t,a,z,m,g,N];
legs=LegsTSUN[q,t,z,m,b,n,N,s,mMax,qMax,TSUNbank];
integrand=IndexVectorAdjUk[q,z,m,N]IndexChiralVecAdjSUk[q,t,z,m,N]*adjHypers*legs;
integrand/.ImposeSUcondition[z,m,N] (* impose SU conditions on U expressions *)
];


AdjHypersSSQ[q_,t_,a_,z_,m_,g_,N_]:=
Module[{prototype,replacementRule,adjHypers},
adjHypers=1;
(* generate prototype*)
If[g>0,
	prototype=IndexHyperAdjSUN[q,t,z,m,a[[1]],N];
	(* copy the prototype g times *)
	Table[
		replacementRule={a[[1]]->a[[i]]};
		adjHypers=adjHypers(prototype/.replacementRule)
	,{i,1,g}];
];
adjHypers
];


LegsTSUN[q_,t_,z_,m_,b_,n_,N_,s_,mMax_,qMax_,TSUNbank_]:=
Module[{verbosityTSUN,prototype,replacementRule,legs,indicesForLegsBank,calcTSUNfromBank},
legs=1;
(* generate prototype*)
If[s>0,

	calcTSUNfromBank=1;
	If[calcTSUNfromBank==0,
		verbosityTSUN=0;
		prototype=IndexTSUN[q,t,z,m,b[[1]],n[[1]],N,mMax,qMax,verbosityTSUN];,
	If[calcTSUNfromBank==1,
		indicesForLegsBank=Table[m[[N]][[k]],{k,1,N-1}];
		(*Print["indicesForLegsBank=",indicesForLegsBank];*)
		prototype=TSUNbank[indicesForLegsBank];
	]];

	(* copy the prototype s times *)
	Table[
		replacementRule=Table[b[[1]][[j]]->b[[i]][[j]],{j,1,N-1}];
		legs=legs(prototype/.replacementRule)
	,{i,1,s}];
];

legs
];


calcTSUNbank[q_,t_,z_,m_,b_,n_,N_,s_,mMax_,qMax_,TSUNbank_,verbosity_]:=
Module[{ind,rank,verbosityTSUN,mCombinations,numCombinations,mGlobalSymFluxesAssignment,mGlobalSymFluxesDefined,res},
rank=N-1;
mCombinations=GenerateCombinationsList[rank,mMax[[N]]];
numCombinations=Length[mCombinations];
Print["Gauge group is SU(N) for N = ",N];
Print["Number of m combinations to calculate for SSQ(N) = ",numCombinations];
Table[
	(*Print["m=",mCombinations\[LeftDoubleBracket]k\[RightDoubleBracket]];*)
	Print["Calculating for the global symmetry fluxes configuration ",k,"/",numCombinations,", m=",mCombinations[[k]]];
	mGlobalSymFluxesAssignment=Table[m[[N]][[i]]->mCombinations[[k]][[i]],{i,1,rank}];
	mGlobalSymFluxesDefined=m/.mGlobalSymFluxesAssignment;
	res=IndexTSUN[q,t,z,mGlobalSymFluxesDefined,b[[1]],n[[1]],N,mMax,qMax,verbosity]//Timing;
	Print["calc time = ",res[[1]], " seconds"];
	TSUNbank[mCombinations[[k]]]=res[[2]];
	(*Print["result = ",res\[LeftDoubleBracket]2\[RightDoubleBracket]];*)
,{k,1,numCombinations}];
Print["Finished initializing TSUNbank"];
];


(* ::Subsection::Closed:: *)
(*End*)


End[]
EndPackage[]
