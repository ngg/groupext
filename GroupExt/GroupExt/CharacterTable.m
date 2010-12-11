GroupExponent[g_?GroupQ] := GroupExponent[g] = Apply[LCM, Map[GroupElementOrder[g, #]&, GroupConjugacyClassRepresentatives[g]]]

GroupCharacterTableDixonPrime[g_] := GroupCharacterTableDixonPrime[g] = Module[{p, e},
	e = GroupExponent[g];
	p = (Floor[(2*Floor[Sqrt[GroupOrder[g]]]-1)/e]+1)*e+1;
	While [!PrimeQ[p], p = p + e];
	p 
] 

GroupCharacterTableMTRow[g_, i_, k_] := GroupCharacterTableMTRow[g, i, k] = Module[{classes, iclass, kelem, x, j, p, ret},
	classes = GroupConjugacyClassRepresentatives[g];
	ret = ConstantArray[0, GroupNumOfConjugacyClasses[g]];
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

GroupCharacterTableMT[g_, i_] := Table[GroupCharacterTableMTRow[g, i, k], {k, 1, GroupNumOfConjugacyClasses[g]}]

GroupCharacterScalarProduct[g_, a_, b_] := Sum[a[[i]]*Conjugate[b[[i]]], {i, Length[a]}]/GroupOrder[g]

GroupCharacterTableSplit[g_, i_, v_] := Module[{r, p, x, m, id, w, j},
	If[Length[v] == 1, Return[{v}]];
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	m = GroupCharacterTableMT[g, i];
	w = Rest[v];
	If[Count[Table[Length[SubspaceIntersection[{m.w[[j]]}, w, Modulus -> p]], {j, Length[w]}], 0] == 0, Return[{v}]];
	id = IdentityMatrix[r];
	Select[
		Map[
			SubspaceIntersection[
				v,
				NullSpace[
					m - #[[1, 2]]*id
				, Modulus -> p],
				Modulus -> p
			] &, 
 			Union[
 				Solve[
 					CharacteristicPolynomial[m, x] == 0
	 			, x, Modulus -> p]
 			]
 		]
	, (Length[#] > 0)&]
]

GroupCharacterTableSplitFirst[g_, i_] := Module[{r, p, x, m, id},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	m = GroupCharacterTableMT[g, i];
	id = IdentityMatrix[r];
	Map[
		RowReduce[
			NullSpace[
				m - #[[1, 2]]*id
			, Modulus -> p],
			Modulus -> p
		] &, 
 		Union[
 			Solve[
 				CharacteristicPolynomial[m, x] == 0
 			, x, Modulus -> p]
 		]
 	]
]

GroupCharacterTableNormalize[g_, a_] := Module[{h, p, s, inv, d, n, x},
	n = GroupOrder[g];
	h = GroupConjugacyClassSizes[g];
	p = GroupCharacterTableDixonPrime[g];
	inv = GroupConjugacyClassInverses[g];
	s = Sum[h[[i]]*a[[i]]*a[[inv[[i]]]], {i, Length[a]}];
	d = Min[Map[#[[1, 2]]&, Solve[n/x^2 == s, x, Modulus -> p]]];
	Mod[a*d, p]
]

GroupCharacterTableFinite[g_] := Module[{x, r, i, p},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	If[r == 1, Return[{{1}}]];
	x = GroupCharacterTableSplitFirst[g, 2];
	Do[
		x = Apply[Union, Map[GroupCharacterTableSplit[g, i, #]&, x]]
	, {i, 3, r}];
	Sort[Map[GroupCharacterTableNormalize[g, #]&, Table[x[[i, 1]], {i, r}]]]
] 

GroupCharacterTable[g_?GroupQ] := GroupCharacterTable[g] = Module[{e, einv, r, p, t, s, i, j, k, l, repr, fin, x, jl, conjprod, smk, smkl},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	e = GroupExponent[g];
	repr = GroupConjugacyClassRepresentatives[g];
	einv = PowerMod[e, -1, p];
	t = (-1)^(2/e);
	s = PowerMod[PrimitiveRoot[p], (p-1)/e, p];
	fin = GroupCharacterTableFinite[g];
	conjprod = GroupConjugacyClassProductTable[g];
	Table[
		Table[
			FullSimplify[
				Sum[
					Mod[
						jl = 1;
						smkl = 1;
						smk = PowerMod[s, -k, p];
						einv*Sum[
							x = Mod[fin[[i, jl]]*smkl, p];
							jl = conjprod[[jl, j]];
							smkl = Mod[smkl*smk, p];
							x
						, {l, 0, e-1}]
					, p]*t^k
				, {k, 0, e-1}]
			]			
		, {j, 1, r}]
	, {i, 1, r}]
] 
