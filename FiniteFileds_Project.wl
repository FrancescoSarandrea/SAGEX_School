(* ::Package:: *)

(* ::Chapter:: *)
(*Finite Fields and Large Ansatze Project*)


(* ::Section::Closed:: *)
(*Part1*)


(* ::Subsection:: *)
(*Useful Functions *)


(* ::Item:: *)
(*Import the BlackBox Function*)


Get["/home/fsarandrea/Wolfram Mathematica/SAGEX_School/BlackBox.wl"];
Get["/home/fsarandrea/Wolfram Mathematica/SAGEX_School/BlackBoxExample.nb"];


(* ::Item:: *)
(*Functions to map  from Z to Q and viceversa*)


rationalReconstruct[a_, n_]:= With[{v=LatticeReduce[{{a,1},{n,0}}][[1]]}, v[[1]]/v[[2]]];
toField[Rational[r_, s_], p_] :=Mod[Mod[r, p]*ModularInverse[s, p], p];


(* ::Item:: *)
(*Define Momentum Twistors to Evaluate Numerical Points*)


Z=RandomInteger[{0,23}, {4,6}];

W[A_, i_, p_]:=Mod[ModularInverse[
               Mod[Dot[{Z[[1,(Mod[(i-2),6]+1)]],Z[[2,(Mod[(i-2),6]+1)]]}, -LeviCivitaTensor[2],{Z[[1,(Mod[i-1,6]+1)]],Z[[2,(Mod[i-1,6]+1)]]}],p]*
               Mod[Dot[{Z[[1,(Mod[i-1,6]+1)]],Z[[2,(Mod[i-1,6]+1)]]}, -LeviCivitaTensor[2],{Z[[1,(Mod[i,6]+1)]],Z[[2,(Mod[i,6]+1)]]}], p],p]*
               Mod[Total[Total[Total[Table[Mod[-LeviCivitaTensor[4][[A,B,C,D]]*Z[[B,(Mod[(i-2),6]+1)]]*Z[[C,(Mod[i-1,6]+1)]]*Z[[D,(Mod[i,6]+1)]], p],
               {D,1,4},
               {C,1,4},
               {B,1,4}]]]], p],p];


helFn[fun_, i_Integer]:=If[MemberQ[fun,i], If[SameQ[Head@fun,spA], 1, -1],0];


(* ::Subsection:: *)
(*Constructing the Ansatz*)


(* ::Item:: *)
(*List of Spinor Brackets*)


$P = 2147483497;
spAList={spA[1,2],spA[2,3],spA[3,4],spA[4,5],spA[5,6],spA[6,1]};
spAList=(Table[spA[i,j], {i,1,6}, {j,i,6}] //Flatten) /.spA[i_,i_]:>Nothing
spBList=spAList /.spA->spB;
monList= Join[spAList, spBList]


(* ::Item:: *)
(*Setting the Conditions on Dimensionality and Helicities*)


dimN=10;
hels={-2,3,-4,0,-4,3};
Table[helN[i]=hels[[i]], {i,6}]
expList=\[Beta][#]&/@Range[Length@monList]


(* ::Item:: *)
(*Find Integer Solutions to the Constraints and Construct the List of Monomials*)


helSums=Table[expList.(helFn[#,i]&/@monList), {i,6}];
solList=Solve[Total[expList]==dimN && hels==helSums, expList, NonNegativeIntegers];
Length@solList


gList=(monList^expList )/.List->Times /.# &/@solList;


(* ::Item:: *)
(*Initialising Phase-Space Points in the Finite Field*)


Do[
Z=RandomInteger[{0,$P-1}, {4,6}];
primePoint[j]=Join[{Table[{Z[[1,i]],Z[[2,i]]}, {i,6}]}, {Table[{W[3,i,$P], W[4,i,$P]}, {i,6}]}];     
, {j,(Length@gList)+1}]


(* ::Item:: *)
(*Finding th basis of monomials*)


arbEvalMat=Table[gList /.{spA[i_, j_]:>Dot[primePoint[k][[1,i]], LeviCivitaTensor[2],primePoint[k][[1,j]]],spB[i_, j_]:>Dot[primePoint[k][[2,i]], -LeviCivitaTensor[2],primePoint[k][[2,j]]]}, {k,1,Length@gList}]; 


reducedMat=RowReduce[arbEvalMat, Modulus->$P];


gBasis=gList[[#]]&/@DeleteCases[Table[Min[Position[reducedMat[[i]],1]], {i,Length@reducedMat}], \[Infinity]];


(* ::InheritFromParent:: *)
(**)


(* ::Item:: *)
(*Checking Momentum Conservation for all the Phase Space Points*)


Table[Total[KroneckerProduct@@@Thread[primePoint[i]]] //Mod[#, $P]&, {i,1,25}]


(* ::Item:: *)
(*Evaluating the Monomial Basisat the different PS points*)


Table[gBasis/.{spA[i_, j_]:>Mod[spinorProduct[primePoint[k][[1,i]] , primePoint[k][[1,j]]], $P],
spB[i_, j_]:>Mod[spinorProduct[primePoint[k][[2,i]], primePoint[k][[2,j]]], $P]}, 
{k,25}];

primeEvals=Mod[%,$P];


primeEvals //MatrixForm


denom = (spB[3, 4]*spB[4, 5]*(spA[2, 1]*spB[1, 5] + spA[2, 6]*spB[6, 5])*(spA[6, 1]*spB[1, 3] + spA[6, 2]*spB[2, 3])*(s[3, 4] + s[4, 5] + s[3, 5]) )/.s[i_, j_]:>spA[i,j]*spB[i,j]


(* ::Item:: *)
(*Solving the Linear System to find the values of the Coefficients*)


blackBoxList=Mod[Table[blackBox[primePoint[i], $P]*Mod[(denom /.{spA[k_, l_]:>Mod[spinorProduct[primePoint[i][[1,k]] , primePoint[i][[1,l]]], $P],
spB[k_, l_]:>Mod[spinorProduct[primePoint[i][[2,k]], primePoint[i][[2,l]]], $P]}), $P], {i,1,Length@primeEvals}], $P];
primeM=Mod[Table[Prepend[primeEvals[[i]], blackBoxList[[i]]], {i,Length@primeEvals}], $P];


primeM //MatrixForm


nullSp=NullSpace[primeM, Modulus-> $P]
ans=rationalReconstruct[#, $P]&/@Flatten[%]


numerator=1/2*gBasis.ans[[2;;]] //Simplify


(* ::Section::Closed:: *)
(*Part2 *)
(**)


Imod=PowerMod[-1,1/2,$P];
sqrt2Mod=PowerMod[2, 1/2, $P];
Mod[4*Imod*2*Imod, $P];
rationalReconstruct[%, $P]


sigmaVec=Table[PauliMatrix[i], {i,0,3}]/.{I->Imod, -I->-Imod};
sigmaVecBar=Join[{IdentityMatrix[2]},-Table[PauliMatrix[i], {i,1,3}]]/. {I->Imod, -I->-Imod};
minkMetr={{1,0,0,0},{0,-1,0,0},{0,0,-1,0},{0,0,0,-1}}; 

gluon[i_, j_, "+"]:=spBAsigma[i,j]/spA[j,i];
gluon[i_, j_, "-"]:=spBAsigma[j,i]/spB[j,i];
(*threeVertex[i_, j_, k_]:>Imod*ModularInverse[4, $P]*Table[(minkMetr[[a1, a2]]*(p[i]-p[j])[[a3]]+minkMetr[[a2, a3]]*(p[j]-p[k])[[a1]]+minkMetr[[a3, a1]]*(p[k]-p[i])[[a2]]), {a1,1,4},{a2,1,4},{a3,1,4}];
fourVertx= Imod*ModularInverse[8,$P]*Table[(2*minkMetr[[a1,a2]]*minkMetr[[a3,a4]]-minkMetr[[a1,a3]]*minkMetr[[a2,a4]]-minkMetr[[a1,a4]]*minkMetr[[a2,a3]]), {a1,1,4},{a2,1,4},{a3,1,4}, {a4,1,4}];*)


helVal[1]="+";
helVal[2]="-";
helVal[3]="+";
helVal[4]="-";
helVal[5]="+";
helVal[6]="-";


(* ::Item:: *)
(*Define a function to evaluate objects numerically*)


Clear[EvaluateNum]


EvaluateNum[p[i_], point_]:=Mod[ModularInverse[2, $P]*Table[Dot[point[[2,i]], sigmaVec[[a]], point[[1,i]]], {a, Length@sigmaVec}], $P]; 
EvaluateNum[spBAsigma[i_,j_], point_]:=Mod[Table[Dot[point[[2,i]], sigmaVecBar[[a]], point[[2,i]]], {a, Length@sigmaVecBar}], $P];
EvaluateNum[spA[i_, j_], point_]:= Mod[Dot[point[[1,i]], LeviCivitaTensor[2], point[[1,j]]], $P];
EvaluateNum[spB[i_, j_], point_]:= Mod[Dot[point[[2,i]], -LeviCivitaTensor[2], point[[2,j]]], $P];
EvaluateNum[s_Plus, point_]:=Module[{lis, res},
lis= s /.Plus->List;
res=Total[Table[EvaluateNum[lis[[a]], point], {a, Length@lis}]];
Return[res];
]
EvaluateNum[-a_, point_]:=-EvaluateNum[a, point];
EvaluateNum[1/d_, point_]:= ModularInverse[(EvaluateNum[d, point]), $P];
EvaluateNum[t_Times, point_]:=Module[{lis, res},
lis= t /.Times->List;
res=Times@@Table[EvaluateNum[lis[[a]], point], {a, Length@lis}];
Return[res];
]
EvaluateNum[contraction[a_,b_], point_]:=Module[{res},
res=Mod[Dot[EvaluateNum[a, point],minkMetr, EvaluateNum[b, point]], $P];
Return[res];
]

EvaluateNum[contr[threeVertex[mom1_, mom2_, mom3_],a_, b_], point_]:=Module[{p1,p2,p3,trVert,aNum, bNum,res},
p1= EvaluateNum[mom1, primePoint[1]];
p2= EvaluateNum[mom2, primePoint[1]];
p3= EvaluateNum[mom3, primePoint[1]];
trVert=Imod*ModularInverse[4, $P]*Table[(minkMetr[[a1, a2]]*(p1-p2)[[a3]]+minkMetr[[a2, a3]]*(p2-p3)[[a1]]+minkMetr[[a3, a1]]*(p3-p1)[[a2]]), {a1,1,4},{a2,1,4},{a3,1,4}];
aNum= Mod[Dot[minkMetr,EvaluateNum[a, point]], $P];
bNum= Mod[Dot[minkMetr,EvaluateNum[b, point]], $P];
res=Mod[Table[Total[Total[Table[trVert[[a1,a2,a3]]*aNum[[a2]]*bNum[[a3]], {a2,1,4},{a3,1,4}]]], {a1,1,4}], $P];
Return[res];
]

EvaluateNum[contr[fourVertx,a_, b_, c_], point_]:=Module[{fourVert,aNum, bNum, cNum,res},
fourVert=Imod*ModularInverse[8,$P]*Table[(2*minkMetr[[a1,a2]]*minkMetr[[a3,a4]]-minkMetr[[a1,a3]]*minkMetr[[a2,a4]]-minkMetr[[a1,a4]]*minkMetr[[a2,a3]]), {a1,1,4},{a2,1,4},{a3,1,4}, {a4,1,4}];
aNum= Mod[Dot[minkMetr,EvaluateNum[a, point]], $P];
bNum= Mod[Dot[minkMetr,EvaluateNum[b, point]], $P];
cNum= Mod[Dot[minkMetr,EvaluateNum[c, point]], $P];
res=Mod[Table[Total[Total[Total[Table[fourVert[[a1,a2,a3,a4]]*aNum[[a2]]*bNum[[a3]]*bNum[[a4]], {a2,1,4},{a3,1,4},{a4,1,4}]]]], {a1,1,4}], $P];
Return[res];
]

(*EvaluateNum[P2[lis_List], point_]:= Module[{ptot, res},
ptot=Total[Table[EvaluateNum[p[i], point], {i, Length@lis}]];
res=Mod[Dot[ptot, minkMetr, ptot], $P];
Return[res];
]

EvaluateNum[(1/(P2[l__])*a__), point_]:=Module[{ptot,sq,res},
ptot=Total[Table[EvaluateNum[p[i], point], {i, Length@lis}]];
sq=Mod[Dot[ptot, minkMetr, ptot], $P];
res=Mod[-Imod*ModularInverse[sq, $P]*Mod[EvaluateNum[a, point], $P], $P];
Return[res];
]*)

EvaluateNum[invP2[a_List]*b__, point_]:=invP2[a]*EvaluateNum[b, point];

EvaluateNum[contr[a__]+contr[b__]+contr[c__], point_]:=EvaluateNum[contr[a], point]+EvaluateNum[contr[b], point]+EvaluateNum[contr[c], point];


(* ::Item:: *)
(*Implementation Checks*)


EvaluateNum[Total[p[#]&/@Range[6]], primePoint[1]] //Mod[#, $P]&


(* ::InheritFromParent:: *)
(**)


(* ::InheritFromParent:: *)
(**)


(* ::Item:: *)
(*Berends-Giele Recursion*)


BerendsGiele[Curr[lis_List, n_Integer]]:=If[n>1,
                                            If[n>2,
                                                 invP2[lis]*(Total[Table[contr[threeVertex[-Total[p[#]&/@lis], Total[p[#]&/@lis[[;;i]]],Total[p[#]&/@lis[[(i+1);;]]]],Curr[lis[[;;i]],Length@lis[[;;i]]],Curr[lis[[(i+1);;]],Length@lis[[(i+1);;]]]],{i,1, (Length@lis-1)}]]+ Total[Total[Flatten[Table[contr[fourVertx, Curr[lis[[;;i]],Length@lis[[;;i]]], Curr[lis[[(i+1);;j]],Length@lis[[(i+1);;j]]], Curr[lis[[(j+1);;]],Length@lis[[(j+1);;]]]],{i,1,(Length@lis-2)},{j,i+1,(Length@lis-1)}]]]]) //Flatten
                                                 
                                                 ,invP2[lis]* Total[Table[contr[threeVertex[-Total[p[#]&/@lis], Total[p[#]&/@lis[[;;i]]],Total[p[#]&/@lis[[(i+1);;]]]],Curr[lis[[;;i]],Length@lis[[;;i]]],Curr[lis[[(i+1);;]],Length@lis[[(i+1);;]]]],{i,1, (Length@lis-1)}]] //Flatten
                                                       
                                                     ]
                                                 , gluon[lis[[1]], Mod[lis[[1]]+1,6]+1, helVal[lis[[1]]]]
                                              ]; 


lis={1,2,3,4,5}
  Total[Total[Flatten[Table[contr[fourVertx, Curr[lis[[;;i]],Length@lis[[;;i]]], Curr[lis[[(i+1);;j]],Length@lis[[(i+1);;j]]], Curr[lis[[(j+1);;]],Length@lis[[(j+1);;]]]],{i,1,(Length@lis-2)},{j,i+1,(Length@lis-1)}]]]]


(((Curr[{1,2,3,4},4]//.Curr[i__, j__]:>BerendsGiele[Curr[i,j]]) /.Plus->List) /. l_List:>Total[l] /; (Head[#]&/@l==Table[p, {i, Length@l}] ||(Head[#]&/@-l==Table[p, {i, Length@l}])) ) //Flatten;
%//.Mod[Times[a__,p2Term[l_List]], p_]:>p2Term[l]*Mod[a,p] 
