GroupExponent[g_?GroupQ] := GroupExponent[g] = Apply[LCM, Map[GroupElementOrder[g, #]&, GroupConjugacyClassRepresentatives[g]]]

GroupCharacterTableDixonPrime[g_] := GroupCharacterTableDixonPrime[g] = Module[{p, e},
	e = GroupExponent[g];
	p = (Floor[(2*Floor[Sqrt[GroupOrder[g]]]-1)/e]+1)*e+1;
	While [!PrimeQ[p], p = p + e];
	p 
] 

GroupCharacterTableMTRow[g_, i_, k_] := GroupCharacterTableMTRow[g, i, k] = Module[{classes, iclass, kelem, x, j, p, ret},
	classes = GroupConjugacyClassRepresentatives[g];
	ret = ConstantArray[0, Length[classes]];
	If[i == 1, Return[ReplacePart[ret, k -> 1]]];
	p = GroupCharacterTableDixonPrime[g];
	If[k == 1, Return[ReplacePart[ret, GroupConjugacyClassNum[g, classes[[i]]^(-1)] -> Mod[GroupConjugacyClassSize[g, classes[[i]]], p]]]];
	classes = GroupConjugacyClassRepresentatives[g];
	iclass = GroupConjugacyClass[g, classes[[i]]];
	kelem = classes[[k]];
	Do[
		j = GroupConjugacyClassNum[g, iclass[[x]]^(-1)**kelem];	
		ret = ReplacePart[ret, j -> Mod[ret[[j]]+1, p]] 
	, {x, Length[iclass]}];
	ret
]

GroupCharacterTableSplit[g_, i_, x_] := Module[{ret},
	ret = {};
	{x}
]

GroupCharacterTableFinite[g_] := GroupCharacterTableFinite[g] = Module[{x, r, i},
	r = Length[GroupConjugacyClassRepresentatives[g]];
	x = {IdentityMatrix[r]};
	Do[
		x = Apply[Union, Map[GroupCharacterTableSplit[g, i, #]&, x]]
	, {i, 2, r}];
	x
	(*Table[x[[i, 1]], {i, r}]*)
] 

GroupCharacterTable[g_?GroupQ] := GroupCharacterTable[g] = Module[{fin},
	fin = GroupCharacterTableFinite[g];
	fin
] 
