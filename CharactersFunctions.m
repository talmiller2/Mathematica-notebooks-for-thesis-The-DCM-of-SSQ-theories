(* ::Package:: *)

(* clean memory *)
(*ClearAll["Global`*"]
Remove["Global`*"]*)

BeginPackage["CharactersFunctions`"]

(* import LieART package *)
Get["C:\\Program Files\\Wolfram Research\\Mathematica\\11.0\\AddOns\\Applications\\LieART\\LieART.m"];

(* define functions to export *)
weightTransMat::usage="retun weightTransMat";
charExpression::usage="retun character expression";
dynkinToIrrep::usage="retun Irrep given Dynkin labels and check the input";
dynkinToChar::usage="retun character given Dynkin labels and check the input";

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

haarMeasure::usage="retun Haar measure";
Options[haarMeasure]={type->"Short"};

innerProd::usage="return group inner product of 2 characters, uses haarMeasure";
innerProdVec::usage="return group inner product vector of term with list of characters";

charPower::usage="return sym/asym power of character";
getCharArgumentPowers::usage="return char with arguments to some power";

getHilbertExpansionCoeffs::usage="return vector of symmetric powers of character after inner product, for the Hilbert series";
getHilbertExpansion::usage="combine coeffs to a taylor expansion";

charToHilbertIntegrand::usage="build polynominal form for the full form of Hilbert series";
calcHilbertIntegral::usage="full calculation of the Hilbert integral by recursively finding poles and residues";





Begin["`Private`"]


(* ::Subsection:: *)
(*Character expression generation*)


weightTransMat[algebraClass_,rank_]:=(
Module[{identity,form1,form2},
(* define transformation matrix to turn WeightSystem[] into the familiar character *)

identity=Table[Table[KroneckerDelta[i,j],{i,1,rank}],{j,1,rank}];

form1 = Table[Table[1,{i,1,rank}],{j,1,rank}];
(*form1[[1]] = Table[1,{i,1,rank}];*)
For[i=2,i<=rank,i++,
For[j=1,j<=rank,j++,
If[j>=i,
form1[[i]][[j]]=-1,
form1[[i]][[j]]=0];
]];

form2 = Table[Table[1,{i,1,rank}],{j,1,rank}];
For[i=2,i<=rank,i++,
For[j=1,j<=rank,j++,
If[j>=i,
form2[[i]][[j]]=1,
form2[[i]][[j]]=0];
]];

(* forms for different groups *)
Switch[algebraClass,
A,(* SU(N) *)
form2,
C,(* Sp(2N) *)
form1,
G2,(* G2 *)
form1,
(* other groups {B,D,F4,E6,E7,E8} not tested yet *)
B||D||F4||E6||E7||E8,
Print["Error: this algebraClass not fully implemented"]
]

])


boxToVec[box_]:=Table[box[[i]],{i,1,Length[box]}]
charExpression[a_,WeightSys_,algebraClass_,rank_]:=(
charComponents=Table[
weightsVecForm=boxToVec[WeightSys[[i]]]; (* if this operation was done in the same line with matrix multiplication, would not work*)
WeightsNewBasis=weightTransMat[algebraClass,rank].weightsVecForm;
\!\(
\*UnderoverscriptBox[\(\[Product]\), \(j = 1\), \(rank\)]\((
\*SuperscriptBox[\(a[\([j]\)]\), \(WeightsNewBasis[\([j]\)]\)])\)\)
,{i,1,Length[WeightSys]}];
Total[charComponents]
)

dynkinToIrrep[repDynkinLabels_,algebraClass_]:=
Module[{rank,statusList,stringDynkin,stringIrrep,stringFull,irrep,algebraClassLocal},
rank = Length[repDynkinLabels];
(* analytically continue Sp(2)=SU(2)=SO(3) *)
If[algebraClass===C && rank==1,
algebraClassLocal=A,
algebraClassLocal=algebraClass];
(* check input for error *)
If[rank==0,
Print["Error: len(repDynkinLabels)=0"],
statusList=Table[Not[Negative[repDynkinLabels[[i]]]]&&IntegerQ[repDynkinLabels[[i]]],{i,1,rank}];
If[Not[AllTrue[statusList,TrueQ]],
Print["Error: repDynkinLabels elements invalid"],
(* get Irrep *)
(*stringDynkin=StringReplace[repDynkinLabels//TextString,{"{"->"[","}"->"]"}];
stringIrrep="Irrep[algebraClass]";
stringFull=StringJoin[stringIrrep,stringDynkin];
irrep=stringFull//ToExpression*)
irrep=Apply[Irrep[algebraClassLocal],repDynkinLabels]
]]
]

dynkinToChar[a_,repDynkinLabels_,algebraClass_]:=
Module[{rank,irrep,WeightSys,algebraClassLocal},
rank = Length[repDynkinLabels];
(* analytically continue Sp(2)=SU(2)=SO(3) *)
If[algebraClass===C && rank==1,
algebraClassLocal=A,
algebraClassLocal=algebraClass];
(* generate irrep and char *)
irrep = dynkinToIrrep[repDynkinLabels,algebraClassLocal];
WeightSys=WeightSystem[irrep];
charExpression[a,WeightSys,algebraClass,rank]
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
Module[{irrepColor,dynkinLabels,irreps,chars},

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
irreps=Table[Style[dynkinToIrrep[dynkinLabels[[i]],algebraClass],FontColor->irrepColor],{i,1,Length[dynkinLabels]}];
irreps=Join[{1},irreps]; (* add the singlet *)

(* create chars *)
chars=Table[dynkinToChar[a,dynkinLabels[[i]],algebraClass]
,{i,1,Length[dynkinLabels]}];
chars=Join[{1},chars]; (* add the singlet *)

{irreps,chars}
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
dynkinLabels={{1,0,0,0},{0,1,0,0},{2,0,0,0},{1,0,0,1},{0,0,0,3},{0,0,1,1},{0,1,0,1},{0,0,2,0},{2,0,0,1},{0,0,0,4},{0,1,1,0},{0,0,1,2},{2,0,1,0},{5,0,0,0},{3,0,0,1},{1,1,0,1},{1,2,0,0},{0,3,0,0},{2,0,0,2},{1,0,2,0},{6,0,0,0},{3,1,0,0}};
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
Module[{irrepColor,dynkinLabels,irreps,chars},

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
irreps=Table[Style[dynkinToIrrep[dynkinLabels[[i]],algebraClass],FontColor->irrepColor],{i,1,Length[dynkinLabels]}];
irreps=Join[{1},irreps]; (* add the singlet *)

(* create chars *)
chars=Table[dynkinToChar[a,dynkinLabels[[i]],algebraClass]
,{i,1,Length[dynkinLabels]}];
chars=Join[{1},chars]; (* add the singlet *)

{irreps,chars}
]


fitIndexWithCharsSSQN[index_,a_,b_,s_,g_,N_,q_,qMaxSSQ_]:=
Module[{indexFit,indexFitTesting,replacements,irreps,chars,innerProdList,bCurr,rankUSp,rankSUN,indexFitSeries},
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
{irreps,chars}=generateIrrepsAndCharsSSQN[bCurr,A,rankSUN,i];
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
Series[IndexFit,{q,0,qMaxSSQ}]//ExpandAll
(*{difference,Series[IndexFit,{q,0,qMaxSSQ}]//ExpandAll}*)
]


fitIndexWithCharsSSQNTiming2[index_,a_,b_,s_,g_,N_,q_,qMaxSSQ_]:=
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
{Series[IndexFit,{q,0,qMaxSSQ}]//ExpandAll,Series[indexFitTesting,{q,0,qMaxSSQ}]}
]


(* ::Subsection:: *)
(*Cartan variable transformations*)


transformationRuleFI[b_,NSU_]:=
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


transformAllFI[index_,b_,NSU_,s_]:=
Module[{indexTemp},
indexTemp=index;
tranformationRule={};
Table[
indexTemp=indexTemp/.transformationRuleFI[b[[i]],NSU];
,{i,1,s}];
indexTemp
]


(* ::Subsection::Closed:: *)
(*Group integration functions*)


haarMeasure[a_,algebraClass_,rank_,OptionsPattern[]]:=
Module[{rankpp},
(*expressions from 
"2017 - Henning, Muruyama et al - Operator bases, S-matrices, and their partition functions", page 85 *)

(* forms for different groups *)
Switch[algebraClass,
A, (* SU(rank+1) *)
rankpp=rank+1;
If[OptionValue[type]=="Short",
(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rankpp\)]\((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\))/.a[[rankpp]]->\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]
\*FractionBox[\(1\), \(a[\([i]\)]\)]\),
If[OptionValue[type]=="Long",
1/rankpp! (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]\((
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rankpp\)]\((\((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\))\)\))/.a[[rankpp]]->\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rankpp - 1\)]
\*FractionBox[\(1\), \(a[\([i]\)]\)]\)]]
,
B, (* SO(2*rank+1) *)
If[OptionValue[type]=="Short",
(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\((1 - a[\([i]\)])\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\)\)),
If[OptionValue[type]=="Long",
1/(rank! 2^rank) (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\(\((1 - a[\([i]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)]\)])\)\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)] a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\)\)\))]]
,
C,(* Sp(2*rank) *)
If[OptionValue[type]=="Short",
(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\((1 - 
\*SuperscriptBox[\(a[\([i]\)]\), \(2\)])\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\)\)),
If[OptionValue[type]=="Long",
1/(rank! 2^rank) (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank\)]\(\((1 - 
\*SuperscriptBox[\(a[\([i]\)]\), \(2\)])\) \((1 - 
\*FractionBox[\(1\), 
SuperscriptBox[\(a[\([i]\)]\), \(2\)]])\)\)\))(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)] a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\)\)\))]]
,
D, (* SO(2*rank) *)
If[OptionValue[type]=="Short",
(\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\))\)\)\)),
If[OptionValue[type]=="Long",
1/(rank! 2^(rank-1)) (\!\(
\*UnderoverscriptBox[\(\[Product]\), \(i = 1\), \(rank - 1\)]\(
\*UnderoverscriptBox[\(\[Product]\), \(j = i + 1\), \(rank\)]\((\((1 - a[\([i]\)] a[\([j]\)])\) \((1 - 
\*FractionBox[\(a[\([i]\)]\), \(a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(1\), \(a[\([i]\)] a[\([j]\)]\)])\) \((1 - 
\*FractionBox[\(a[\([j]\)]\), \(a[\([i]\)]\)])\))\)\)\))]]

(* dont have expressions for the exceptionals {G2,F4,E6,E7,E8}, should be added *)
]]



(* ::Subsection::Closed:: *)
(*Group Inner product*)


innerProd[a_,char1_,char2_,algebraClass_,rank_]:=(
InnnerProdTable=Table[
(* initialize prod *)
InnnerProdTmp=If[i==1,haarMeasure[a,algebraClass,rank]*char1*char2,InnnerProdTmp];
(* recursively use Coefficient[] (contour integral Subscript[da, i]/2Subscript[\[Pi]\[ImaginaryI]a, i]) *)
InnnerProdTmp=Coefficient[InnnerProdTmp,a[[i]],0] 
,{i,1,rank}] ;
(* return last value of table, after all integrals are done*)
InnnerProdTable[[-1]] 
)

innerProdVec[a_,term_,bankChars_,algebraClass_,rank_]:=Table[
currChar=bankChars[[i]];
innerProd[a,term,currChar,algebraClass,rank]
,{i,Length[bankChars]}]


(* ::Subsection:: *)
(*Symmetrization of characters*)


charPower[a_,char_,rank_,order_,type_]:=(
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
]
For[i=1,i<=order-1,i++,
M[[i]][[i+1]]=i;
For[j=i+1,j<=order,j++,
M[[j]][[i]]=c[[j-i+1]];
];
];
(*Clear[c]; Print[M//MatrixForm];*)
Det[M]/order!
)
getCharArgumentPowers[a_,char_,rank_,order_]:=(
Table[
charModified=char;
For[i=1,i<=rank,i++,
charModified=charModified/.a[[i]]-> a[[i]]^k];
charModified
,{k,1,order}]
)



(* ::Subsection:: *)
(*Hilbert series related*)


(* ::Subsubsection::Closed:: *)
(*Expansion in r*)


getHilbertExpansionCoeffs[a_,char_,algebraClass_,rank_,rOrderMax_]:=Table[
Print[i,"/",rOrderMax];
charMod=charPower[a,char,rank,i,"sym"];
innerProd[a,1,charMod,algebraClass,rank]
,{i,1,rOrderMax}]

getHilbertExpansion[coeffs_,r_]:=1+Total[Table[coeffs[[i]]r^i,{i,1,Length[coeffs]}]]



(* ::Subsubsection:: *)
(*Hilbert integrand*)


charToHilbertIntegrand[a_,r_,char_,rank_]:=(
Module[{overallCoeff,charClean,charListFull,numTerms,charToPolyTerm,
exponentVec,componentVec,component,coeff,multiplicity},
If[Length[char]==0, (* treatment of singlet char *)
1/(1-r)^char,
(* treatment of normal chars *)
overallCoeff=FactorTermsList[char][[1]];
charClean=FactorTermsList[char][[2]];
charListFull= charToList[charClean];
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


(* ::Subsubsection::Closed:: *)
(*Hilbert full contour integral solution*)


calcHilbertIntegral[a_,r_,term_,level_,rank_,verbosity_,method_]:=
Module[{dummy,denom,termList,currsol,poles,polesNoDup,acceptedAbsVal,res,resNum,currPole,residues,termSimplified},

Print["level = ", level];
If[verbosity==1,
Print["curr term = ", term]];

(* get term and break apart the denominator to monomials *)
Clear[dummy]; (* dummy var to help in the case of simple denominator *)
denom=dummy*Denominator[term];
termList=Activate[List@@Inactivate[denom]];

(* find poles *)
poles=Flatten[Table[
currsol=Solve[termList[[i]]==0,a[[level]],Method->Reduce];
(* test if solution is in a form of ConditionalExpression *)
Table[
(*Print["currsol\[LeftDoubleBracket]j\[RightDoubleBracket]=",currsol\[LeftDoubleBracket]j\[RightDoubleBracket]]*)
If[ StringMatchQ[TextString[a[[level]]/.currsol[[j]]],"ConditionalExpression[*"],
{a[[level]]->(a[[level]]/.currsol[[j]])[[1]]},
currsol[[j]]]
,{j,1,Length[currsol]}]
,{i,1,Length[termList]}]
];
polesNoDup=DeleteDuplicates[poles];
Print["num poles = ", Length[polesNoDup], " (with duplicates ",Length[poles], ")"];
If[verbosity==1,
Print["polesNoDup list = ", polesNoDup]];

(* filter for poles that are AbsValue\[GreaterEqual]1 *)
acceptedAbsVal=Table[
currPole=Refine[(a[[level]]/.polesNoDup[[i]]),r>0];
If[NumericQ[currPole]&&currPole==0,(* deal with pole at 0 exception *)
1,
If[Exponent[currPole,r]>0,1,0]
]
,{i,1,Length[polesNoDup]}];
If[verbosity==1,
Print["poles accepted due to abs value list = ", acceptedAbsVal]];


(* in case no poles are found, this branch is zero  *)
If[Length[poles]==0,
Print["no poles, residue is 0"]; 
0,

(* calcualte residues for all poles *)
residues=Table[
If[acceptedAbsVal[[i]]==0 ,
0,
If[verbosity==1,
Print["curr residue num = ", i, "/", Length[polesNoDup], ", pole = ", {polesNoDup[[i]]}],
Print["curr residue num = ", i, "/", Length[polesNoDup]]
];
res=Residue[term,{a[[level]],a[[level]]/.polesNoDup[[i]]}];
(* res=res//Simplify; *)
If[verbosity==1,
Print["curr residue full expression = ", res]];
(* test if Residue failed *)
If[StringMatchQ[TextString[res],"Residue[*"],
Print["Residue failed: ", res]];
(* check if problematic value *)
resNum=res/.r->0.5;
Table[resNum=resNum/.a[[k]]->1,{k,1,Length[rank]}];
If[resNum===ComplexInfinity||resNum===Indeterminate,
Print["Residue result problematic: ", res];
Print["Originated from term = ", term];
Print["full poles list = ", polesNoDup];
Print["problematic pole = ", polesNoDup[[i]]];
];
res
]
,{i,1,Length[polesNoDup]}];


Switch[method,

"Simplify",
(* combining all the residues of current level *)
Print["summing and simplyfing the residues"];
termSimplified=residues//Total//FullSimplify;

(* next level *)
If[level<rank,
calcHilbertIntegral[a,r,termSimplified,level+1,rank,verbosity,method]
, (* following is for level=rank, last recursion level *)
termSimplified
] (* must not end with ; *)
,

"Branches",
(* recursion step for each calculated residue *)
If[level<rank,
Table[
Print["level: ", level, ", pole number: ", i, "/" ,Length[polesNoDup]];
If[NumericQ[residues[[i]]]==True && residues[[i]]==0,
If[verbosity==1,
Print["residue=0 return 0"]];
0,
calcHilbertIntegral[a,r,residues[[i]],level+1,rank,verbosity,method]
]
,{i,1,Length[polesNoDup]}]
, (* following is for level=rank, last recursion level *)
residues
] (* must not end with ; *)
]

]
]


End[]
EndPackage[]
