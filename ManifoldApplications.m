(* ::Package:: *)

(* ::Input:: *)
(**)


BeginPackage["ManifoldApplications`","Global`"]
GeometricQuantities::usage="Returns a list of geometric quantities on a specified manifold.
There are two (2) required arguments:
1) The metric tensor of the manifold, as a matrix
2) The coordinates of the manifold, as a vector
Optionally, as a third argument, one can pass a list of assumptions to be made throughout the local scope of the calculation.
(Default: {})
Optionally, as a fourth argument, one can specify whether Simplify[] shall be used on some of the more complicated intermediate quantities.
(Default: True. Use False if performance becomes an issue.)
Optionally, as a fifth argument, one can specify whether Print[] statements shall be used after intermediary calculations.
(Default: False. Use True if milestones are desired for longer calculations.) 

The function will return a vector of the following mathematical objects,
pre-supposing the connection to be the Levi-Civita connection.
1) The Ricci Scalar
2) The Levi-Civita connection, as a matrix
3) The Ricci Tensor, as a matrix
4) The Einstein Tensor, as a matrix
5) Whether the manifold is Einstein (True/False), i.e. whether the Ricci Scalar is coordinate-independent"

FisherMetric::usage="Returns the Fisher Metric of a univariate probability distribution.
There are three (3) required arguments:
1) The distribution, as an anonymous function
2) The parameters of the distribution, which form the coordinates of the Fisher Metric space,
as a vector
3) The limits of integration for the random variable, as a two-element vector
Optionally, as a fourth argument, one can pass a list of assumptions to be made throughout the local scope of the calculation.
(Default: {})"

Der::usage="Returns the coordinate Derivative of an arbitrary tensor.
There are two (2) required arguments:
1) The tensor, as a matrix
2) The coordinates of the manifold, as a vector"

CovD::usage="Returns the Covariant Derivative of an arbitrary tensor.
There are four (4) required arguments:
1) The tensor, as a matrix
2) The index of the tensor, as a list of the form {\[PlusMinus]1,\[PlusMinus]1,...},
where -1 indicates a covariant (lower) index and +1 represents a contravariant (upper) index
3) The coordinates of the manifold, as a vector
4) The Christoffel symbols (connection coefficients) associated with the covariant derivative, as a matrix"

Begin["Private`"]

Der[Tensor_,Coordinates_]:=
Module[
{\[Xi]=Tensor,r=Coordinates,rank,cycle,d\[Xi]},

If[ArrayQ[\[Xi]],rank=ArrayDepth[\[Xi]],rank=0];
(*rank of the derivative tensor will be one higher than rank of Tensor*)
cycle=Prepend[Range[rank],rank+1];
(*this will permute the indices to match the canonical form*)
d\[Xi]=Transpose[D[\[Xi],#]&/@r,cycle];

Return[d\[Xi]]
]

GeometricQuantities[Metric_,Coordinates_,$Assumptions_:{},Simplified_:True,Prolix_:False]:=
Module[
{g=Metric,r=Coordinates,invg,dg,\[CapitalGamma],d\[CapitalGamma],Riem,Ric,\[ScriptCapitalR],\[ScriptCapitalG],EinsteinQ},

invg=Inverse[g]//Simplify;
If[Prolix,Print["Inverse metric calculated"]];
dg=Der[g,r];
(*Subscript[(dg), ijk]=\!\(
\*SubscriptBox[\(\[PartialD]\), \(k\)]
\*SubscriptBox[\(g\), \(ij\)]\) == Subscript[g, ij,k]*)

\[CapitalGamma]=1/2 invg.(dg+Transpose[dg,{1,3,2}]-Transpose[dg,{2,3,1}])//Simplify;
If[Prolix,Print["Christoffel symbols calculated"]];
d\[CapitalGamma]=Der[\[CapitalGamma],r];
(*Subscript[(d\[CapitalGamma])^i, jkm]=\!\(
\*SubscriptBox[\(\[PartialD]\), \(m\)]
\*SubscriptBox[
SuperscriptBox[\(\[CapitalGamma]\), \(i\)], \(jk\)]\)=Subscript[\[CapitalGamma]^i, jk,m]*)

Riem=Transpose[d\[CapitalGamma],{1,2,4,3}]-Transpose[d\[CapitalGamma],{1,2,3,4}]+Transpose[\[CapitalGamma].\[CapitalGamma],{1,3,2,4}]- Transpose[\[CapitalGamma].\[CapitalGamma],{1,4,2,3}];
If[Simplified,Riem=Simplify[Riem]];
If[Prolix,Print["Riemann tensor calculated"]];

Ric=Tr[Transpose[Riem,{1,3,2,4}],Plus,2];
If[Simplified,Ric=Simplify[Ric]];
If[Prolix,Print["Ricci tensor calculated"]];

\[ScriptCapitalR]=Tr[invg.Ric];
If[Simplified,\[ScriptCapitalR]=Simplify[\[ScriptCapitalR]]];
If[Prolix,Print["Ricci scalar calculated"]];

EinsteinQ=And[##]&@@(FreeQ[\[ScriptCapitalR],#]&/@r);
(*an Einstein metric will have Ricci scalar independent of all coordinates, i.e. constant over the manifold*)
\[ScriptCapitalG]=Ric-1/2 \[ScriptCapitalR] g;
If[Simplified,\[ScriptCapitalG]=Simplify[\[ScriptCapitalG]]];

Return[{\[ScriptCapitalR],\[CapitalGamma],Ric,\[ScriptCapitalG],EinsteinQ}]
]

FisherMetric[Distribution_,Parameters_,Limits_,$Assumptions_:{}]:=
Module[
{p=Distribution,\[Beta]=Parameters,\[ScriptL],\[ScriptG],metric},

If[!(Integrate[p[x],{x,##}&@@Limits]===1),Return[{"Improper Normalization",p[x]}]];
\[ScriptL][x]=Log[p[x]];
\[ScriptG][x]=-D[\[ScriptL][x],{\[Beta],2}]//FullSimplify;
(*In practice, this provides a massive speed-up over the (\[PartialD]/\[PartialD]\[Beta]^i)(ln p[x;\[Beta]])(\[PartialD]/\[PartialD]\[Beta]^j)(ln p[x;\[Beta]]) form.*)
metric=Integrate[\[ScriptG][x]p[x],{x,##}&@@Limits]//FullSimplify;

Return[metric]
]

CovD[Tensor_,Index_,Coordinates_,ChristoffelSymbols_]:=
Module[
{\[Xi]=Tensor,i=Index,r=Coordinates,\[CapitalGamma]=ChristoffelSymbols,rank,\[Sigma],p1,p2,p\[Gamma],d\[Xi],\[Delta]\[Xi],D\[Xi]},

If[ArrayQ[\[Xi]],rank=ArrayDepth[\[Xi]],rank=0];
If[!(Length[i]==rank),Return["Improper index specified, rank mismatch."]];
If[!And[##]&@@(MemberQ[{-1,1},#]&/@i),Return["Improper index signature. Please specify -1 for covariant and +1 for covariant indices."]]
\[Sigma]=Range[rank];
p1=Table[Insert[\[Sigma][[;;-2]],\[Sigma][[-1]],j],{j,1,rank}];
p2=Table[Append[Drop[\[Sigma],{j}],\[Sigma][[j]]],{j,1,rank}];
p\[Gamma]={{2,3,1},{1,2,3}};
d\[Xi]=Der[\[Xi],r];
\[Delta]\[Xi]=-Sum[Transpose[i[[k]]*Transpose[\[Xi],p1[[k]]].Transpose[\[CapitalGamma],p\[Gamma][[i[[k]]]]],p2[[k]]],{k,1,rank}];
D\[Xi]=d\[Xi]-\[Delta]\[Xi]//Simplify;

Return[D\[Xi]]
]

End[]

EndPackage[]


