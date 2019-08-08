(* ::Package:: *)

(* clean memory *)
(*ClearAll["Global`*"]
Remove["Global`*"]*)

BeginPackage["CharactersFunctions`"]

(* import LieART package *)
Get["C:\\Program Files\\Wolfram Research\\Mathematica\\11.0\\AddOns\\Applications\\LieART\\LieART.m"];

(* define functions to export *)
weightTransMat::usage="retun weightTransMat"
transformWeightsList::usage="transform a list of weights using weightTransMat";
charExpression::usage="retun character expression";
charExpressionGeneralTransMat::usage="retun character expression (for an input transformation matrix)";

dynkinToIrrep::usage="retun Irrep given Dynkin labels and check the input";
dynkinToChar::usage="retun character given Dynkin labels and check the input";
checkAlgebraClass::usage="check the Lie algebra class input";

generateDynkinLabels::usage="retun list of Dynkin labels for certain algebraClass and rank";
generateIrrepsAndChars::usage="retun irreps and chars for certain algebraClass and rank";
fitIndexWithChars::usage="fit computed index to USp(2g) and SU(2) characters";
fitIndexWithCharsTiming::usage="fitIndexWithChars that also prints its run-time";

generateDynkinLabelsSSQN::usage="retun list of Dynkin labels for certain algebraClass and rank";
generateIrrepsAndCharsSSQN::usage="retun irreps and chars for certain algebraClass and rank";
fitIndexWithCharsSSQN::usage="fit computed index to USp(2g) and SU(N) characters";
fitIndexWithCharsSSQNTiming::usage="fitIndexWithChars that also prints its run-time"
fitIndexWithCharsSSQNTiming2::usage="fitIndexWithChars that also prints its run-time";
transformationRuleFI::usage="transformation rule for the b's (of FI terms) to a different basis";
transformAllFI::usage="transformation rule for the FI in all the legs";

haarMeasure::usage="define Haar measure (based on formulas for algebras A,B,C,D,G2 only)";
Options[haarMeasure]={type->"Short"};
haarMeasureGeneric::usage="define Haar measure (generic for all Lie groups)";
Options[haarMeasureGeneric]={type->"Short"};

innerProd::usage="return group inner product of 2 characters, uses haarMeasure";
innerProdVec::usage="return group inner product vector of term with list of characters";

charPower::usage="return sym/asym power of character";
getCharArgumentPowers::usage="return char with arguments to some power";

getHilbertExpansionCoeffs::usage="return vector of symmetric powers of character after inner product, for the Hilbert series";
getHilbertExpansion::usage="combine coeffs to a taylor expansion";

charToHilbertIntegrand::usage="build polynominal form for the full form of Hilbert series";
calcHilbertIntegralMain::usage="full calculation of the Hilbert integral by recursively finding poles and residues";
calcHilbertIntegral::usage="full calculation of the Hilbert integral by recursively finding poles and residues";

calcNumericDivergence::usage="For a Hilbert integral result given in components that are hard to simplify, calculate the divergence degree numerically";




Begin["`Private`"]


(* ::Subsection:: *)
(*Character expression generation*)


updateRank[algebraClass_,rank_]:=
If[algebraClass===A || algebraClass===B || algebraClass===C || algebraClass===D,
	rank
,
	Which[	
		algebraClass===E6,
			6,	
		algebraClass===E7,
			7,
		algebraClass===E8,
			8,		
		algebraClass===F4,
			4,				
		algebraClass===G2,	
			2,	
		True, 
			Print["Invalid algebraClass=", algebraClass]
		]
]


weightTransMat[algebraClass_,rank_]:=
Module[{identity,form1,form2,form3,form4,i,j,errorMessege},
(* define transformation matrix to turn WeightSystem[] into standard forms of characters in different Lie groups *)

identity=Table[Table[KroneckerDelta[i,j],{i,1,rank}],{j,1,rank}];

(* matrix for Sp (algebraClass=C) and G2 *)
form1 = Table[Table[1,{i,1,rank}],{j,1,rank}];
(*form1[[1]] = Table[1,{i,1,rank}];*)
For[i=2,i<=rank,i++,
	For[j=1,j<=rank,j++,
		If[j>=i,
			form1[[i]][[j]]=-1,
			form1[[i]][[j]]=0
		];
	]
];

(* matrix for SU, algebraClass=A *)
form2 = Table[Table[1,{i,1,rank}],{j,1,rank}];
For[i=2,i<=rank,i++,
	For[j=1,j<=rank,j++,
		If[j>=i,
			form2[[i]][[j]]=1,
			form2[[i]][[j]]=0
		];
	]
];

(* matrix for SO(2N+1), algebraClass=B*)
form3 = form2;
For[i=1,i<=rank,i++,
	form3[[i]][[rank]]=1/2;
];

(* matrix for SO(2N), algebraClass=D *)
form4 = form2;
For[i=1,i<=rank,i++,
	form4[[i]][[rank-1]]=1/2;
	form4[[i]][[rank]]=1/2;
];
form4[[rank]][[rank-1]]=-1/2;

(* forms for different groups *)
errorMessege="Error: this algebraClass not implemented";
Which[
	algebraClass===A,(* SU(N) *)
		form2,
	algebraClass===B,(* SO(2N+1) for N\[GreaterEqual]3 *)
		form3,		
	algebraClass===C,(* Sp(2N) *)
		form2,
	algebraClass===D,(* SO(2N) for N\[GreaterEqual]4 *)
		form4,	
	algebraClass===G2,(* G2 *)
		form1,
	algebraClass===F4,(* F4 *)
		identity,
	algebraClass===E6,(* E6 *)
		identity,
	algebraClass===E7,(* E7 *)
		identity,
	algebraClass===E8,(* E8 *)
		identity,
	True, (* the Else in an ElseIf statement *)
		Print["Invalid algebraClass"]
]
]


boxToList[box_]:=Table[box[[i]],{i,1,Length[box]}]


boxListToNormalList[box_]:=Table[boxToList[box[[i]]],{i,1,Length[box]}]


transformWeightsList[algebraClass_,rank_,weightsBoxList_]:=
Module[{weightsList},
weightsList=boxListToNormalList[weightsBoxList];
Table[
	weightTransMat[algebraClass,rank].weightsList[[i]]
,{i,1,Length[weightsList]}]
]


charExpression[a_,WeightSys_,algebraClass_,rank_]:=
Module[{charComponents,weightsListNewBasis},
weightsListNewBasis=transformWeightsList[algebraClass,rank,WeightSys];
charComponents=Table[
	\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(rank\)]\((
\*SuperscriptBox[\(a[\([j]\)]\), \(\(weightsListNewBasis[\([i]\)]\)[\([j]\)]\)])\)\)
,{i,1,Length[WeightSys]}];
Total[charComponents]
]


charExpressionGeneralTransMat[a_,WeightSys_,algebraClass_,rank_,weightTransMat_]:=
Module[{charComponents,WeightsNewBasis,weightsList},
weightsList=boxListToNormalList[WeightSys];
charComponents=Table[
	WeightsNewBasis=weightTransMat.weightsList[[i]];
	\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(rank\)]\((
\*SuperscriptBox[\(a[\([j]\)]\), \(WeightsNewBasis[\([j]\)]\)])\)\)
,{i,1,Length[WeightSys]}];
Total[charComponents]
]


dynkinToIrrep[repDynkinLabels_,algebraClass_]:=
Module[{rank,statusList,stringDynkin,stringIrrep,stringFull,irrep,algebraClassLocal},
rank = Length[repDynkinLabels];

(* check algebra input *)
algebraClassLocal=checkAlgebraClass[repDynkinLabels,algebraClass];

(* check Dynkin labels input *)
If[rank==0,
	Print["Error: len(repDynkinLabels)=0 meaning rank=0 invalid."],
	statusList=Table[Not[Negative[repDynkinLabels[[i]]]]&&IntegerQ[repDynkinLabels[[i]]],{i,1,rank}];
	If[Not[AllTrue[statusList,TrueQ]],
		Print["Error: repDynkinLabels elements invalid"]
	,
		(* get Irrep *)
		irrep=Apply[Irrep[algebraClassLocal],repDynkinLabels]
	]
]
]


dynkinToChar[a_,repDynkinLabels_,algebraClass_]:=
Module[{rank,irrep,WeightSys,algebraClassLocal},
rank = Length[repDynkinLabels];

(* check algebra input *)
algebraClassLocal=checkAlgebraClass[repDynkinLabels,algebraClass];

(* generate irrep and char *)
irrep=dynkinToIrrep[repDynkinLabels,algebraClassLocal];
WeightSys=WeightSystem[irrep];
charExpression[a,WeightSys,algebraClass,rank]

]


checkAlgebraClass[repDynkinLabels_,algebraClass_]:=
Module[{rank,algebraClassLocal},
rank = Length[repDynkinLabels];

algebraClassLocal=algebraClass;

(* Map Sp(2) and SO(3) to SU(2) (LieART definition) *)
If[algebraClass===C && rank==1, algebraClassLocal=A];
If[algebraClass===B && rank==1, algebraClassLocal=A];

(* Map SO(5) to Sp(4) (LieART definition) *)
If[algebraClass===B && rank==2, algebraClassLocal=C];

(* Map SO(6) to SU(4) (LieART definition) *)
If[algebraClass===D && rank==3, algebraClassLocal=A];

(* SO(N) for N<7 not allowed (LieART definition) *)
If[ ( algebraClassLocal===B && rank<=2 ) || ( algebraClassLocal===D && rank<=3 ),
	Print["SO(N) for N<7 not allowed in LieART definition."]
];

algebraClassLocal
]


(* ::Subsection:: *)
(*Irreps generation and character fitting, for SSQ(2)*)


generateDynkinLabels[algebraClass_,rank_]:=
Module[{dynkinLabels,zerosList,dynkin001,maxSU2rep},

(*
If[algebraClass===C && rank>1,
dynkinLabels={{1,0},{0,1},{2,0},{0,2},{1,1},{3,0},{0,3},{2,1},{4,0}};
If[rank>2,
zerosList=Table[0,{k,1,rank-2}];
dynkinLabels=Table[Join[dynkinLabels[[i]],zerosList],{i,1,Length[dynkinLabels]}];
];
*)

If[algebraClass===C && rank==2,
dynkinLabels={{1,0},{0,1},{2,0},{0,2},{1,1},{3,0},{0,3},{2,1},{4,0}}
];
If[algebraClass===C && rank>2,
dynkinLabels={{1,0,0},{0,1,0},{0,0,1},{2,0,0},{0,2,0},{1,1,0},{3,0,0},{0,3,0},{2,1,0},{4,0,0}};
If[rank>3,
zerosList=Table[0,{k,1,rank-3}];
dynkinLabels=Table[Join[dynkinLabels[[i]],zerosList],{i,1,Length[dynkinLabels]}];
]];


(* for algebraClass\[Equal]A, rank irrelevant because we use SU(2) only *)
If[algebraClass===A||(algebraClass===C && rank==1),
maxSU2rep=10;
dynkinLabels=Table[{i},{i,1,maxSU2rep}];
];

dynkinLabels
]


generateIrrepsAndChars[a_,algebraClass_,rank_]:=
Module[{irrepColor,dynkinLabels,irreps,irrepsDims,irrepsStyled,chars},

(* define Dynkin labels *)
dynkinLabels=generateDynkinLabels[algebraClass,rank];

(* create irreps *)
If[algebraClass===C,irrepColor=Blue];
If[algebraClass===A,
If[rank==1,irrepColor=Red,
If[rank==2,irrepColor=Green,
If[rank==3,irrepColor=Purple,
If[rank==4,irrepColor=Cyan,
If[rank==5,irrepColor=Yellow,irrepColor=Magenta
]]]]]];

irreps=Table[dynkinToIrrep[dynkinLabels[[i]],algebraClass],{i,1,Length[dynkinLabels]}];
irrepsDims=Table[Length[WeightSystem[irreps[[i]]]],{i,1,Length[dynkinLabels]}];
irrepsStyled=Table[Style[irreps[[i]],FontColor->irrepColor],{i,1,Length[dynkinLabels]}];

irrepsDims=Join[{1},irrepsDims]; (* add the singlet *)
irrepsStyled=Join[{1},irrepsStyled]; (* add the singlet *)

(* create chars *)
chars=Table[dynkinToChar[a,dynkinLabels[[i]],algebraClass],{i,1,Length[dynkinLabels]}];
chars=Join[{1},chars]; (* add the singlet *)

Print["irreps=",irreps];
Print["irrepsDims=",irrepsDims];
Print["irrepsStyled=",irrepsStyled];

{irrepsStyled,irrepsDims,chars}
]


fitIndexWithChars[index_,a_,b_,s_,g_,q_,qMaxSSQ_]:=
Module[{indexTemp,irreps,chars,innerProdList,bCurr},
indexTemp=index;

(* fitting USp(2g) characters *)
If[g>0,
	{irreps,chars}=generateIrrepsAndChars[a,C,g];
	innerProdList=innerProdVec[a,indexTemp,chars,C,g];
	indexTemp=Total[innerProdList*irreps];
];

(* fitting SU(2)^s characters *)
If[s>0,
	Table[
		bCurr={b[[i]]};
		{irreps,chars}=generateIrrepsAndChars[bCurr,A,i];
		innerProdList=innerProdVec[bCurr,indexTemp,chars,A,1];
		indexTemp=Total[innerProdList*irreps];
	,{i,1,s}];
];

Series[indexTemp//ExpandAll,{q,0,qMaxSSQ}]

]


fitIndexWithCharsTiming[index_,a_,b_,s_,g_,q_,qMaxSSQ_]:=
Module[{IndexFit},
IndexFit=fitIndexWithChars[index,a,b,s,g,q,qMaxSSQ]//Timing;
Print["Fit calculation time = ", IndexFit[[1]], " seconds" ];
IndexFit[[2]]
]


(* ::Subsection:: *)
(*Irreps generation and character fitting, for SSQ(N)*)


generateDynkinLabelsSSQN[algebraClass_,rank_]:=
Module[{dynkinLabels,zerosList,dynkin001,maxSU2rep,dynkinLabelsConjugateReps},

(* fitting the a's with USp(2g) reps *)
If[algebraClass===C && rank==2, (* USp(4) *)
(*dynkinLabels={{1,0},{0,1},{2,0},{0,2},{1,1},{3,0},{0,3},{2,1},{4,0}};*)
dynkinLabels={{1,0},{0,1},{2,0},{0,2},{1,1},{3,0},{0,3},{2,1},{4,0},{1,2},{0,4},{5,0},{3,1},{1,3},{2,2}};
];
If[algebraClass===C && rank>2, (* USp(6) and above *)
dynkinLabels={{1,0,0},{0,1,0},{0,0,1},{2,0,0},{3,0,0},{1,1,0},{1,0,1},{0,0,2},{0,2,0},{0,1,1},{4,0,0},{2,1,0},{2,0,1}};
(*dynkinLabels={{1,0,0},{0,1,0},{0,0,1},{2,0,0},{3,0,0},{1,1,0},{1,0,1},{0,0,2},{0,2,0},{0,1,1},{4,0,0}};*)
If[rank>3,
zerosList=Table[0,{k,1,rank-3}];
dynkinLabels=Table[Join[dynkinLabels[[i]],zerosList],{i,1,Length[dynkinLabels]}];
]];

(* fitting the b's with SU(N) reps *)
If[(algebraClass===A && rank==1)||(algebraClass===C && rank==1), (* SU(2) or USp(2) *)
(*dynkinLabels={{1},{2},{3},{4},{5}};*)
dynkinLabels=Table[{i},{i,1,10}];
];
If[algebraClass===A && rank==2, (* SU(3) *)
(*dynkinLabels={{1,0},{2,0},{1,1},{3,0},{2,1},{4,0},{0,5},{1,3},{2,2},{6,0},{4,1},{7,0}};*)
(*dynkinLabels={{1,0},{2,0},{1,1},{3,0},{2,1},{4,0},{0,5},{1,3},{2,2},{6,0},{4,1},{7,0},{3,2},{0,8},{5,1},{9,0},{2,4},{1,6},{3,3},{10,0},{0,11},{7,1},{5,2},{4,3},{12,0},{8,1},{6,2}}*)
dynkinLabels={{1,0},{2,0},{1,1},{3,0},{2,1},{4,0},{0,5},{1,3},{2,2},{6,0},{4,1},{7,0},{3,2},{0,8},{5,1},{9,0},{2,4},{1,6},{3,3},{10,0},{0,11},{7,1},{5,2},{4,3},{12,0},{8,1},{6,2},{13,0},{3,5},{1,9},{0,14},{4,4},{2,7}}
(*dynkinLabels={{1,0},{0,1},{2,0},{0,2},{1,1},{3,0},{0,3},{2,1},{1,2},{4,0},{0,5},{1,3},{2,2},{6,0},{4,1},{7,0},{3,2},{0,8},{5,1},{9,0},{2,4},{1,6},{3,3},{10,0}}*);
];
If[algebraClass===A && rank==3, (* SU(4) *)
(*dynkinLabels={{1,0,0},{0,1,0},{2,0,0},{1,0,1},{0,1,1},{0,2,0},{0,0,3},{4,0,0},{2,0,1},{2,1,0},{0,3,0},{5,0,0},{1,2,0},{1,1,1},{3,0,1}};*)
(*dynkinLabels={{1,0,0},{0,1,0},{2,0,0},{1,0,1},{0,1,1},{0,2,0},{0,0,3},{4,0,0},{2,0,1},{2,1,0},{0,3,0},{5,0,0},{1,2,0},{1,1,1},{3,0,1},{2,0,2},{3,1,0},{6,0,0},{0,4,0},{1,0,4}};*)
dynkinLabels={{1,0,0},{0,1,0},{2,0,0},{1,0,1},{0,1,1},{0,2,0},{0,0,3},{4,0,0},{2,0,1},{2,1,0},{0,3,0},{5,0,0},{1,2,0},{1,1,1},{3,0,1},{2,0,2}};
];
If[algebraClass===A && rank==4, (* SU(5) *)
(*dynkinLabels={{1,0,0,0},{0,1,0,0},{2,0,0,0},{1,0,0,1},{0,0,0,3},{0,0,1,1},{0,1,0,1},{0,0,2,0},{2,0,0,1},{0,0,0,4},{0,1,1,0},{0,0,1,2},{2,0,1,0}};*)
(*dynkinLabels={{1,0,0,0},{0,1,0,0},{2,0,0,0},{1,0,0,1},{0,0,0,3},{0,0,1,1},{0,1,0,1},{0,0,2,0},{2,0,0,1},{0,0,0,4},{0,1,1,0},{0,0,1,2},{2,0,1,0},{5,0,0,0},{3,0,0,1},{1,1,0,1},{1,2,0,0},{0,3,0,0},{2,0,0,2},{1,0,2,0},{6,0,0,0},{3,1,0,0}};*)
dynkinLabels={{1,0,0,0},{0,1,0,0},{2,0,0,0},{1,0,0,1},{0,0,0,3},{0,0,1,1},{0,1,0,1},{0,0,2,0},{2,0,0,1},{0,0,0,4},{0,1,1,0},{0,0,1,2},{2,0,1,0},{5,0,0,0},{3,0,0,1},{1,1,0,1},{1,2,0,0},{0,3,0,0},{2,0,0,2},{1,0,2,0},{6,0,0,0},{3,1,0,0},{1,1,1,0},{3,0,1,0},{0,2,1,0},{1,0,0,4},{7,0,0,0}}
];
If[algebraClass===A && rank>=5, (* SU(6) and above *)
Print["Error: algebraClass==A with rank>=5 currently invalid"];
];

If[algebraClass===A && rank>=2,
dynkinLabelsConjugateReps=Table[Reverse[dynkinLabels[[i]]],{i,1,Length[dynkinLabels]}];
dynkinLabels=Join[dynkinLabels,dynkinLabelsConjugateReps];
dynkinLabels=DeleteDuplicates[dynkinLabels];
];

dynkinLabels
]


generateIrrepsAndCharsSSQN[a_,algebraClass_,rank_,indLeg_]:=
(* For USp(2g) chars rank=g and indLeg is irrelevant, for SU(N) chars rank=N-1 and indLeg is for different legs*)
Module[{irrepColor,dynkinLabels,irreps,chars,irrepsDims,irrepsStyled},

(* define Dynkin labels *)
dynkinLabels=generateDynkinLabelsSSQN[algebraClass,rank];

(* create irreps *)
If[algebraClass===C,irrepColor=Blue];
If[algebraClass===A,
If[indLeg==1,irrepColor=Red,
If[indLeg==2,irrepColor=Green,
If[indLeg==3,irrepColor=Purple,
If[indLeg==4,irrepColor=Cyan,
If[indLeg==5,irrepColor=Yellow,
irrepColor=Magenta
]]]]]];

irreps=Table[dynkinToIrrep[dynkinLabels[[i]],algebraClass],{i,1,Length[dynkinLabels]}];
irrepsDims=Table[Length[WeightSystem[irreps[[i]]]],{i,1,Length[dynkinLabels]}];
irrepsStyled=Table[Style[irreps[[i]],FontColor->irrepColor],{i,1,Length[dynkinLabels]}];

irrepsDims=Join[{1},irrepsDims]; (* add the singlet *)
irrepsStyled=Join[{1},irrepsStyled]; (* add the singlet *)

(* create chars *)
chars=Table[dynkinToChar[a,dynkinLabels[[i]],algebraClass],{i,1,Length[dynkinLabels]}];
chars=Join[{1},chars]; (* add the singlet *)

{irrepsStyled,irrepsDims,chars}
]


fitIndexWithCharsSSQN[index_,a_,b_,s_,g_,N_,q_,qMaxSSQ_]:=
Module[{indexFit,indexFitTesting,replacements,irreps,chars,innerProdList,bCurr,rankUSp,rankSUN,indexFitSeries,irrepsDims},
indexFit=index;
replacements={};

(* fitting USp(2g) characters *)
If[g>0,
rankUSp=g;
{irreps,chars}=generateIrrepsAndCharsSSQN[a,C,rankUSp,0];
(*Print["{irreps,chars}=",{irreps,chars}];*)
innerProdList=innerProdVec[a,indexFit,chars,C,rankUSp];
indexFit=Total[innerProdList*irreps];
replacements=Join[replacements,Table[irreps[[j]]->chars[[j]],{j,1,Length[chars]}]];
];

(* fitting SU(N)^s characters *)
If[s>0,
rankSUN=N-1;
Table[
bCurr=b[[i]];
{irreps,irrepsDims,chars}=generateIrrepsAndCharsSSQN[bCurr,A,rankSUN,i];
(*Print["{irreps,chars}=",{irreps,chars}];*)
innerProdList=innerProdVec[bCurr,indexFit,chars,A,rankSUN];
indexFit=Total[innerProdList*irreps];
replacements=Join[replacements,Table[irreps[[j]]->chars[[j]],{j,1,Length[chars]}]];
,{i,1,s}];
];

(* outputs *)
indexFitTesting=indexFit/.replacements;
indexFitSeries=Series[indexFit//ExpandAll,{q,0,qMaxSSQ}]//Normal;
{indexFitSeries,indexFitTesting}
]


fitIndexWithCharsSSQNTiming[index_,a_,b_,s_,g_,N_,q_,qMaxSSQ_]:=
Module[{res,fitTime,IndexOutput,IndexFit,indexFitTesting,difference},
res=fitIndexWithCharsSSQN[index,a,b,s,g,N,q,qMaxSSQ]//Timing;
fitTime=res[[1]];
Print["Fit calculation time = ", fitTime, " seconds" ];
IndexOutput=res[[2]];
IndexFit=IndexOutput[[1]];
indexFitTesting=IndexOutput[[2]];

(* Testing fitted index same as input index *)
difference=(indexFitTesting-index)//Simplify;
If[difference===0,
Print["Index fit ", Style["passed",FontColor->Green], " consistency test (fit-index=0)"];
,
Print["Index fit ", Style["FAILED",FontColor->Red], " consistency test (fit-index!=0)"];
Print["difference = ", difference];
];

(* Return the fit in pretty irrep form *)
(*{Series[IndexFit,{q,0,qMaxSSQ}]//ExpandAll,Series[indexFitTesting,{q,0,qMaxSSQ}]}*)
Series[IndexFit,{q,0,qMaxSSQ}]//ExpandAll
]


(* ::Subsection:: *)
(*T[SU(N)] legs maximal torus variables transformation*)


transformationRuleFIold[b_,NSU_]:=
Module[{pMat,x1,x2,x3,x4,tranformationRule},
If[NSU<2,Print["N<2 not supported"]];
If[NSU==2,pMat={{2,0,0,0},{0,0,0,0},{0,0,0,0},{0,0,0,0}}];
If[NSU==3,pMat={{1,-1,0,0},{1,2,0,0},{0,0,0,0},{0,0,0,0}}];
If[NSU==4,pMat={{1,-1,0,0},{1,2,1,0},{-1,-1,-2,0},{0,0,0,0}}];
If[NSU==5,pMat={{1,-1,0,0},{1,2,1,1},{-1,-1,-2,-1},{0,0,1,-1}}];
If[NSU>5,Print["N>5 not supported"]];
tranformationRule={b[[1]]->x1,b[[2]]->x2,b[[3]]->x3,b[[4]]->x4}/.{x1->b[[1]]^pMat[[1]][[1]] b[[2]]^pMat[[1]][[2]] b[[3]]^pMat[[1]][[3]] b[[4]]^pMat[[1]][[4]],x2->b[[1]]^pMat[[2]][[1]] b[[2]]^pMat[[2]][[2]] b[[3]]^pMat[[2]][[3]] b[[4]]^pMat[[2]][[4]] ,x3->b[[1]]^pMat[[3]][[1]] b[[2]]^pMat[[3]][[2]] b[[3]]^pMat[[3]][[3]] b[[4]]^pMat[[3]][[4]],x4->b[[1]]^pMat[[4]][[1]] b[[2]]^pMat[[4]][[2]] b[[3]]^pMat[[4]][[3]] b[[4]]^pMat[[4]][[4]] };
tranformationRule
]


transformationRuleFI[b_,NSU_]:=
Module[{transformationMatrix,x,trans1,trans2,rank,tranformationRule},
If[NSU<2,Print["N<2 not supported"]];
If[NSU>5,Print["N>5 not supported"]];

transformationMatrix={{1,-1,0,0},{1,2,1,1},{-1,-1,-2,-1},{0,0,1,-1}};
rank=NSU-1;
tranformationRule=Table[b[[i]]->\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(rank\)]
\*SuperscriptBox[\(b[\([j]\)]\), \(transformationMatrix[\([i, j]\)]\)]\),{i,1,rank}];
tranformationRule
]


transformAllFI[index_,b_,NSU_,s_]:=
Module[{indexTemp},
indexTemp=index;
Table[
indexTemp=indexTemp/.transformationRuleFI[b[[i]],NSU];
,{i,1,s}];
indexTemp
]


(* ::Subsection:: *)
(*Group integration functions*)


haarMeasure[a_,algebraClass_,rank_,OptionsPattern[]]:=
Module[{rankpp,haarPartial,errorMessege,typeHaar,haar},
(*expressions for classical Lie groups from 
"2017 - Henning, Muruyama et al - Operator bases, S-matrices, and their partition functions", page 84, Appendix B.2 *)
typeHaar=OptionValue[type];

(* forms for different groups *)
errorMessege="Error: this algebraClass not implemented";
haarPartial=Which[
	algebraClass===U1, (* U1 group *)
		1,
	algebraClass===A, (* SU(rank+1) *)
		rankpp=rank+1;
		If[typeHaar=="Short",
			(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rankpp\)]\((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\))/.a[[rankpp]]->\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]
\*FractionBox[\(1\), \(a[\([i]\)]\)]\),
		If[typeHaar=="Long",
			1/rankpp! (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rankpp\)]\((\((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\))\)\))/.a[[rankpp]]->\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]
\*FractionBox[\(1\), \(a[\([i]\)]\)]\)]],

	algebraClass===B, (* SO(2*rank+1) *)
		If[typeHaar=="Short",
			(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\((1 - a[\([i]\)])\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\)\)),
		If[typeHaar=="Long",
			1/(rank! 2^rank) (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\(\((1 - a[\([i]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)]\)])\)\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)] a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\)\)\))]],
	algebraClass===C,(* Sp(2*rank) *)
		If[typeHaar=="Short",
			(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\((1 - 
\*SuperscriptBox[\(a[\([i]\)]\), \(2\)])\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\)\)),
		If[typeHaar=="Long",
			1/(rank! 2^rank) (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\(\((1 - 
\*SuperscriptBox[\(a[\([i]\)]\), \(2\)])\) \((1 - 
\*FractionBox[\(1\), 
SuperscriptBox[\(a[\([i]\)]\), \(2\)]])\)\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)] a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\)\)\))]],

	algebraClass===D, (* SO(2*rank) *)
		If[typeHaar=="Short",
			(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\)\)),
		If[typeHaar=="Long",
			1/(rank! 2^(rank-1)) (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)] a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\)\)\))]],
	algebraClass===G2,(* G2 *)
		Print[errorMessege],
	algebraClass===F4,(* F4 *)
		Print[errorMessege],
	algebraClass===E6,(* E6 *)
		Print[errorMessege],
	algebraClass===E7,(* E7 *)
		Print[errorMessege],
	algebraClass===E8,(* E8 *)
		Print[errorMessege],
	True, (* the Else in an ElseIf statement *)
		Print["Invalid algebraClass"]
];
haar=haarPartial/\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\(a[\([i]\)]\)\);
haar
]



haarMeasureGeneric[a_,algebraClass_,rank_,OptionsPattern[]]:=
Module[{typeHaar,WeylDim,algebraClassLong,rootsNum,rootsNewBasis,rootsAll,roots,rootsList,rankUpdated},
typeHaar=OptionValue[type];
rankUpdated=updateRank[algebraClass,rank];

If[algebraClass===U1, (* U(1) group has special treatment *)
	1/a[[1]]
,
	(* Define the algebra class including the rank *)
	If[algebraClass===A || algebraClass===B || algebraClass===C || algebraClass===D,
		algebraClassLong=ToExpression[StringJoin[ToString[algebraClass],ToString[rankUpdated]]];
	,
		algebraClassLong=algebraClass;
	];

	(* Define the relevant roots *)
	Which[
		typeHaar=="Long",
			roots=RootSystem[algebraClassLong];
			rootsList=boxListToNormalList[roots];
			roots=DeleteCases[rootsList,Table[0,{i,1,rankUpdated}]]; (* remove zero roots *)
			
			(* Define the dimension of the Weyl group *)
			WeylDim=Which[
				algebraClass===A, 
					(rank+1)!,
				algebraClass===B || algebraClass===C,	
					rank!*2^rank,
				algebraClass===D,	
					rank!*2^(rank-1),		
				algebraClass===E6,	
					72*6!,
				algebraClass===E7,
					72*8!,
				algebraClass===E8,
					192*10!,			
				algebraClass===F4,
					1152,					
				algebraClass===G2,	
					12,		
				True, 
					Print["Invalid algebraClass=", algebraClass]
			];
	,
		typeHaar=="Short",
			roots=PositiveRoots[algebraClassLong];
			WeylDim=1;
	,
		True,
			Print["Invalid type for Haar measure. type=", typeHaar]
	];
	rootsNewBasis=transformWeightsList[algebraClass,rankUpdated,roots];
	rootsNum=Length[rootsNewBasis];
	1/(WeylDim*\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankUpdated\)]\(a[\([i]\)]\)\)) \!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(rootsNum\)]\((1 - 
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankUpdated\)]\((
\*SuperscriptBox[\((a[\([i]\)])\), \(\(rootsNewBasis[\([j]\)]\)[\([i]\)]\)])\))\)\)
]
]



(* ::Subsection:: *)
(*Group Inner product*)


innerProd[a_,char1_,char2_,algebraClass_,rank_]:=
Module[{InnnerProdTable,InnnerProdTmp},
InnnerProdTable=Table[
	(* initialize prod *)
	InnnerProdTmp=If[i==1,haarMeasureGeneric[a,algebraClass,rank]*char1*char2,InnnerProdTmp];
	(* recursively use Coefficient[] (contour integral Subscript[da, i]/2Subscript[\[Pi]\[ImaginaryI]a, i]) *)
	InnnerProdTmp=Coefficient[InnnerProdTmp,a[[i]],-1] 
,{i,1,rank}];
(* return last value of table, after all integrals are done*)
InnnerProdTable[[-1]] 
]


innerProdVec[a_,term_,bankChars_,algebraClass_,rank_]:=
Module[{currChar},
Table[
	currChar=bankChars[[i]];
	innerProd[a,term,currChar,algebraClass,rank]
,{i,Length[bankChars]}]
]


(* ::Subsection:: *)
(*Symmetrization of characters*)


charPower[a_,char_,rank_,order_,type_]:=
Module[{c,i,M,j,charModified},
(* for chars that are multiplicaitions of different Cartan variables, rank=total number of variables *)
(* based on https://math.stackexchange.com/questions/84103/characters-of-symmetric-and-antisymmetric-powers *)

(* define building blocks*)
c=getCharArgumentPowers[a,char,rank,order];
If [type=="sym",
For[i=1,i<=order,i++,
c[[i]]=(-1)^(i+1) c[[i]]]
];
(* define matrix*)
M=Table[Table[0,{j,1,order}],{i,1,order}];
For[i=1,i<=order,i++,
M[[i]][[i]]=c[[1]];
];
For[i=1,i<=order-1,i++,
M[[i]][[i+1]]=i;
For[j=i+1,j<=order,j++,
M[[j]][[i]]=c[[j-i+1]];
];
];
(*Clear[c]; Print[M//MatrixForm];*)
Det[M]/order!
]


getCharArgumentPowers[a_,char_,rank_,order_]:=
Module[{charModified,i},
Table[
charModified=char;
For[i=1,i<=rank,i++,
charModified=charModified/.a[[i]]-> a[[i]]^k];
charModified
,{k,1,order}]
]


(* ::Subsection:: *)
(*Hilbert series related*)


(* ::Subsubsection::Closed:: *)
(*Expansion in r*)


getHilbertExpansionCoeffs[a_,char_,algebraClass_,rank_,rOrderMax_]:=
Module[{charMod,i},
Table[
Print[i,"/",rOrderMax];
charMod=charPower[a,char,rank,i,"sym"];
innerProd[a,1,charMod,algebraClass,rank]
,{i,1,rOrderMax}]
]


getHilbertExpansion[coeffs_,r_]:=1+Total[Table[coeffs[[i]]r^i,{i,1,Length[coeffs]}]]


(* ::Subsubsection::Closed:: *)
(*Hilbert integrand*)


charToHilbertIntegrand[a_,r_,char_,rank_]:=(
Module[{overallCoeff,charClean,charListFull,numTerms,charToPolyTerm,
exponentVec,componentVec,component,coeff,multiplicity},
If[Length[char]==0, (* treatment of singlet char *)
1/(1-r)^char,
(* treatment of normal chars *)
overallCoeff=FactorTermsList[char][[1]];
charClean=FactorTermsList[char][[2]];
charListFull=charToList[charClean];
numTerms=Length[charListFull];
charToPolyTerm=Range[numTerms];
Table[
exponentVec=Range[rank];
componentVec=Table[
(* initialize component as a term in the fullcharacter *)
component=If[i==1,charListFull[[j]],component];
(* recursively decompose the component *)
exponentVec[[i]]=Exponent[component,a[[i]]] ;
component=Coefficient[component,a[[i]],exponentVec[[i]]] 
,{i,rank}] ;
(* last value of table is the coefficient, after all a's are removed *)
coeff=componentVec[[-1]];
(* The char component can be reconstrcted if we want, coeff\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]
\*SuperscriptBox[\(a\[LeftDoubleBracket]i\[RightDoubleBracket]\), \(exponentVec\[LeftDoubleBracket]i\[RightDoubleBracket]\)]\) *)
(* transform the component to required form *)
multiplicity=coeff;
charToPolyTerm[[j]]=1/(1-r \!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]
\*SuperscriptBox[\(a[\([i]\)]\), \(exponentVec[\([i]\)]\)]\))^multiplicity;
,{j,numTerms}] ;
(* multiply all terms for final result *)
(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(numTerms\)]\(charToPolyTerm[\([j]\)]\)\))^overallCoeff
]])



charToList[char_]:=List@@char


(* ::Subsubsection:: *)
(*Hilbert full contour integral solution*)


calcHilbertIntegralMain[a_,r_,term_,rank_,verbosity_,method_]:=
Module[{levelFirst,calcTime,result},
levelFirst=1;
{calcTime,result}=calcHilbertIntegral[a,r,term,levelFirst,rank,verbosity,method]//Timing;
Print["Hilbert series calculation time = ", calcTime, " seconds = ", calcTime/60^2, " hours"];
If[method=="Branches",result//Flatten//Total,result]
]


calcHilbertIntegral[a_,r_,term_,level_,rank_,verbosity_,method_]:=
Module[{dummy,denom,termList,currsol,poles,polesNoDup,acceptedAbsVal,res,resNum,currPole,
residues,termSimplified,polesRelevant,failedResiduesIndices,faildResExist,nextLevelResidues,returnValue,
failedBranchesIndices,healthyBranchesIndices,allBranches,sickTermsSum,newBranch,healthyBranches,healthyBranchesUpdated},

(* Stating what we are currently working on *)
Print[Style["Level = "<>ToString[level],Bold]];
If[verbosity==1, Print["Current term = ", term]];

(* get term and break apart the denominator to monomials *)
Clear[dummy]; (* dummy var to help in the case of simple denominator *)
denom=dummy*Denominator[term];
termList=Activate[List@@Inactivate[denom]];

(* find poles *)
poles=Flatten[Table[
	currsol=Solve[termList[[i]]==0,a[[level]],Method->Reduce]//Quiet;
	(* test if solution is in a form of ConditionalExpression *)
	Table[
		If[ StringMatchQ[TextString[a[[level]]/.currsol[[j]]],"ConditionalExpression[*"],
			{a[[level]]->(a[[level]]/.currsol[[j]])[[1]]}
		,
			currsol[[j]]
		]
	,{j,1,Length[currsol]}]
,{i,1,Length[termList]}]
];

(* remove duplicates of poles *)
polesNoDup=DeleteDuplicates[poles];
If[verbosity==1, 
	Print["Total number of poles = ", Length[polesNoDup], " (with duplicates ",Length[poles], ")"];
	Print["Poles list (without dupicates) = ", polesNoDup]
];

(* filter for poles that have absolute value\[LessEqual]1 (inside the contour) *)
acceptedAbsVal=Table[
	currPole=Refine[(a[[level]]/.polesNoDup[[i]]),r>0];
	If[NumericQ[currPole]&&currPole==0,(* deal with pole at 0 exception *)
		1
	,
		If[Exponent[currPole,r]>0,1,0]
	]
,{i,1,Length[polesNoDup]}];
If[verbosity==1, Print["Flag the poles accepted due to abs value = ", acceptedAbsVal]];

(* create list of only the relevant poles *)
polesRelevant={};
Table[
	If[acceptedAbsVal[[i]]==1, polesRelevant=Join[polesRelevant,{polesNoDup[[i]]}]; ]
,{i,1,Length[polesNoDup]}];

Print["Number of relevant poles = ", Length[polesRelevant]];
If[verbosity==1, Print["Relevant poles list = ", polesRelevant]; ];

(* in case no poles are found, this branch is zero  *)
If[Length[poles]==0,
	If[verbosity==1, Print["No poles on this branch, therefore integrating this branch gives zero."]];
	0
,
	(* calcualte residues for all poles *)
	faildResExist=0;
	residues={};
	Do[
		If[verbosity==1,
			Print["Calculating residue for pole ", i, "/", Length[polesRelevant], " in level ", level, ", pole is at = ", {polesRelevant[[i]]}],
			Print["Calculating residue for pole ", i, "/", Length[polesRelevant], " in level ", level]
		];
		res=Residue[term,{a[[level]],a[[level]]/.polesRelevant[[i]]}];
		If[verbosity==1, Print["Current residue output full expression = ", res]];
		
		(* test if Residue failed *)
		If[StringMatchQ[TextString[res],"Residue[*"],
			Print[Style["Residue calculation failed.",Bold]];
			faildResExist=faildResExist+1;
			Break[]
		];
		
		(* check if problematic value (Don't remember why this test was necesasry...) *)
		(*
		resNum=res/.r->0.5;
		Table[resNum=resNum/.a[[k]]->1,{k,1,Length[rank]}];
		Print["resNum=",resNum];
		If[resNum===ComplexInfinity||resNum===Indeterminate,
			Print["Residue with a problematic value: ", res];
			Print["Originated from term = ", term];
			Print["full relevant poles list = ", polesRelevant];
			Print["the problematic pole = ", polesRelevant[[i]]];
		];
		*)

		residues=Join[residues,{res}];
	,{i,1,Length[polesRelevant]}];
	
	(* choose the calculation method *)
	Switch[method,
	"Simplify",
		If[faildResExist>0, 
		(* if any failed, no reason to continue the calculation *)
			Print["Failed residue exists in level ", level, ", return \"failed\" flag"];
			"failed"
		, 
			(* combining all the residues of current level *)
			Print["Summing and simplyfing the residues"];
			termSimplified=residues//Total//FullSimplify;

			(* next level *)
			If[level<rank,
				Print["Sending result to level ",  level+1];
				calcHilbertIntegral[a,r,termSimplified,level+1,rank,verbosity,method]
			, (* following is for level=rank, last recursion level *)
				termSimplified
			] (* must not end with ; *)
		]
	,
	"Branches",
		(* recursion step for each calculated residue *)
		If[faildResExist>0, 
			(* if any failed, return to previous level immediately *)
			Print["Failed residue exists in level ", level, ", return \"failed\" flag"];
			"failed"
		, 
			If[level<rank,
				failedBranchesIndices={};
				healthyBranchesIndices={};
				allBranches=Table[
					If[NumericQ[residues[[i]]]==True && residues[[i]]==0,
						Print["Residue for pole ", i, "/", Length[polesRelevant], " in level ", level, " is zero."];
						0
					,
						Print["Residue for pole ", i, "/", Length[polesRelevant], " in level ", level, " is non-zero, sending to level ",  level+1];
						nextLevelResidues=calcHilbertIntegral[a,r,residues[[i]],level+1,rank,verbosity,method];
						If[nextLevelResidues==="failed",
							(* accumulate all branches that will fail in deeper levels *)
							failedBranchesIndices=Join[failedBranchesIndices,{i}];
						,
							healthyBranchesIndices=Join[healthyBranchesIndices,{i}];
							nextLevelResidues
						]
					]
				,{i,1,Length[polesRelevant]}];
				healthyBranches=Table[ allBranches[[healthyBranchesIndices[[i]]]] ,{i,1,Length[healthyBranchesIndices]}];
				
				(* if any branches failed try to fix, otherwise return all branches *)		
				If[Length[failedBranchesIndices]>0,
					Print["Accumulated sick branches ", failedBranchesIndices, "/", Length[polesRelevant], " in level", level];
					
					(* if any future branches failed, sum and simply them, and resend to next level *)
					Print["Summing and simplifying the sick branches."];
					sickTermsSum = Table[ residues[[failedBranchesIndices[[i]]]] ,{i,1,Length[failedBranchesIndices]}];
					sickTermsSum=sickTermsSum//Total//FullSimplify;
					
					Print["Resending to level", level+1];
					newBranch=calcHilbertIntegral[a,r,sickTermsSum,level+1,rank,verbosity,method];
					
					(* check if still failed, in which case return failed to previous level *)	
					If[newBranch==="failed",
						Print["Remedying the sick braches failed at level ",level];
						"failed"
					,
						(* if succeeded, join the lists of healthy branches and return *)
						Print["Forming a new list of healty branches in level ", level];
						healthyBranchesUpdated=Join[healthyBranches,{newBranch}];
						healthyBranchesUpdated
					]
				,			
					allBranches	
				]						
			, (* following is for level=rank, last recursion level simply return all values back up the tree *)
				residues			
			] (* must not end with ; *)
		]		
	]
]
]


End[]
EndPackage[]


(* ::Subsubsection:: *)
(*Numeric evaluation of divergence*)


calcNumericDivergence[hilbertComponents_]:=
Module[{vecLen,precision,rVec,k,calcTime,vectorResults,dataLogLog,dataLogLogPlot,dataLog,lineFitLog,fitLogLogPlot,x},
vecLen=8;
precision=100;
rVec=N[Table[1-10^-k,{k,1,vecLen}],precision];
{calcTime,vectorResults}=Table[hilbertComponents/.r->rVec[[k]]//Flatten//Total//Abs,{k,1,vecLen}]//Timing;
dataLogLog=Table[{1-rVec[[k]],Log[vectorResults[[k]]]},{k,1,vecLen}];
dataLogLogPlot=ListLogLinearPlot[dataLogLog,Joined->True,PlotMarkers->Automatic];
dataLog=Table[{Log[1-rVec[[k]]],Log[vectorResults[[k]]]},{k,1,vecLen}];
lineFitLog=Fit[dataLog,{x,1},x] ;
Print["Numeric divergence degree is ", Coefficient[lineFitLog,x]//N];
Show[dataLogLogPlot,Frame->True,ImageSize->Small]
]


(* ::Input:: *)
(**)
