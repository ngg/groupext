BeginPackage["GroupExt`"]

(* list of public functions with usages *)
NullQ::usage = ""
GroupQ::usage = "GroupQ[g] determines whether g is a group or not."
SubspaceIntersection::usage = ""
GroupIdentity::usage = ""
GroupElementOrder::usage = ""
GroupExponent::usage = ""
GroupConjugatesQ::usage = ""
GroupConjugacyClassRepresentatives::usage = ""
GroupNumOfConjugacyClasses::usage = ""
GroupConjugacyClassSizes::usage = ""
GroupConjugacyClassSize::usage = ""
GroupConjugacyClassRepresentative::usage = ""
GroupCharacterTable::usage = ""
GroupCharacterScalarProduct::usage = ""
GroupElementFromImage::usage = ""
GroupElementFromImages::usage =

Begin["GroupExt`Private`"]

(* there is no proper way to determine if something is null *)
NullQ[x_] := ToString[x] == "Null" && !StringQ[x]

(* we only deal with permutation groups so identity element is always an empty cycle *)
GroupIdentity[g_?GroupQ] := Cycles[{}]

(* in Mathematica 8.0.0 there is a bug that crashes GroupCentralizer[] if called with the identity element (fixed in 8.0.1) *)
Off[General::shdw]
GroupExt`GroupCentralizer[g_, x_] := If[GroupIdentity[g] == x, g, System`GroupCentralizer[g, x]]
On[General::shdw]

(* we declare our error messages here *)
General::notelement = "`1` is not element of `2`"

(* only way to check if something is a group is with a list like this *)
GroupQ[g_] := False
GroupQ[g_] := True /; MemberQ[{
	PermutationGroup, GroupStabilizer, GroupSetwiseStabilizer, GroupCentralizer,
	SymmetricGroup, AlternatingGroup, CyclicGroup, AbelianGroup,
	DihedralGroup, MathieuGroupM11, MathieuGroupM12, MathieuGroupM22,
	MathieuGroupM23, MathieuGroupM24, JankoGroupJ1, JankoGroupJ2,
	JankoGroupJ3, JankoGroupJ4, HigmanSimsGroupHS, ConwayGroupCo1,
	ConwayGroupCo2, ConwayGroupCo3, McLaughlinGroupMcL, SuzukiGroupSuz,
	HeldGroupHe, RudvalisGroupRu, FischerGroupFi22, FischerGroupFi23,
	FischerGroupFi24Prime, TitsGroupT, ONanGroupON, HaradaNortonGroupHN,
	ThompsonGroupTh, LyonsGroupLy, BabyMonsterGroupB, MonsterGroupM
}, Head[g]]

(* we extend some operators here to work with permutations and groups *)

ClearAttributes[NonCommutativeMultiply, Protected]
	(* multiplication of two permutations with ** operator (we can't use *, because Mathematica assumes * is commutative), example: Cycles[{{1,2}}]**Cycles[{{2,3}}] = Cycles[{{1,3,2}}] *)
	NonCommutativeMultiply[x_Cycles, y_Cycles] := PermutationProduct[x, y]
SetAttributes[NonCommutativeMultiply, Protected]

ClearAttributes[Power, Protected]
	(* raising permutations to a power with ^ operator, example: Cycles[{{1,2}}]^3 = Cycles[{{1,2}}] *)
	Power[x_Cycles, n_Integer] := PermutationPower[x, n]

	(* determine where an element is moved by a permutation with ^ operator, example 1^Cycles[{{1,2}}] = 2 *)
	Power[n_Integer, a_Cycles] := PermutationReplace[n, a]

	(* calculate orbit of an element with ^ operator, example 1^PermutationGroup[{Cycles[{{1,2}}], Cycles[{{3,4}}]}] = {1,2} *)
	Power[n_Integer, g_?GroupQ] := GroupOrbits[g, {n}][[1]]

	(* conjugaction of elements with ^ operator, example: Cycles[{{1,2}}]^Cycles[{{2,3}}] = Cycles[{{1,3}}] *)
	Power[x_Cycles, y_Cycles] := y^(-1)**x**y

	(* conjugaction of an element with a whole group with ^ operator, example: Cycles[{{1,2}}]^PermutationGroup[{Cycles[{{1,2}}], Cycles[{{1,4}}]}] =  *)
	Power[x_Cycles, g_?GroupQ] := Union[x^GroupElements[g]]
SetAttributes[Power, Protected]

(* for speed reasons, we don't check if a is in g or not *)
GroupElementOrder[g_?GroupQ, a_] := PermutationOrder[a]

(* TODO *)
GroupElementFromImage[g_?GroupQ, a_Integer, b_Integer] := Module[{lk = 1, ln = 1, sn, s = GroupGenerators[g], l = {Cycles[{}] -> a}, c, x, i},
	Catch[
		sn = Length[s];
		While[lk <= ln,
			Do[
	 			c = l[[lk, 1]] ** s[[i]];
				x = l[[lk, 2]]^s[[i]];
				If[x == b, Throw[c]];
				If[Position[l, x, 2] == {},
					l = Append[l, c -> x];
					ln = ln + 1
				]
			,{i, sn}];
			lk = lk + 1
		];
		Null
	]
]

(* TODO *)
GroupElementFromBaseImages[sc_, base_, basen_, img_] := Module[{i, x, ret = Cycles[{}]},
	Catch[
		Do[
			If[!NullQ[img[[i]]],
				x = GroupElementFromImage[sc[[i,2]], base[[i]], img[[i]]^(ret^(-1))];
				If[NullQ[x], Throw[Null]];
				ret = x**ret
			]
		,{i, basen}];
		ret
	]
]

(* TODO *)
GroupElementFromImages[g_?GroupQ, s_] := Module[{sc, wantedbase, base, basen, ret, i, x},
	Catch[
		wantedbase = Map[First, s];
		sc = GroupStabilizerChain[g, GroupActionBase -> wantedbase];
		basen = Position[sc, PermutationGroup[{}]][[1, 1]] - 1;
		base = sc[[basen + 1, 1]];
		ret = GroupElementFromBaseImages[sc, base, basen, Map[(x = Position[wantedbase, #]; If [Length[x] == 0, Null, s[[x[[1,1]], 2]]])&, base]];
		If[NullQ[ret], Throw[Null]];
		Do[If[s[[i, 1]]^ret != s[[i, 2]], Throw[Null]], {i,1,Length[s]}];
		ret
	]
]

(* TODO *)
GroupConjugatesQBT[a_, b_, sc_, base_, cangoto_, follow_, img_] := Module[{e, imgn, newimg = img, basen, i, next},
	Catch[
		imgn = Length[newimg];
		basen = Length[base];
		While[imgn < basen && follow[[imgn+1]],
			next = newimg[[imgn]]^b;
			If [Position[newimg, next, 1] != {}, Throw[False]];
			newimg = Append[newimg, next];
			imgn = imgn + 1;
		];
		If[imgn == basen,
			e = GroupElementFromBaseImages[sc, base, basen, newimg];
			If[!NullQ[e] && a^e == b, True, False]
		, (* else *)
			Catch[
				Do[
					next = cangoto[[imgn+1, i]];
					If [Position[newimg, next, 1] == {},
						If[GroupConjugatesQBT[a, b, sc, base, cangoto, follow, Append[newimg, next]] == True, Throw[True]];
					];
				,{i,Length[cangoto[[imgn+1]]]}];
				False
			]
		]
	]
]

(* we have an inner version of GroupConjugatesQ that doesn't check if a,b are elements of g *)
(* TODO *)
GroupConjugatesQInner[g_, a_, b_] := Module[{as, bs, i, sc, basen, base, cangoto, follow, pos, bcyclelen, set, len},
	Catch[
		set = Union[Flatten[Map[#[[1]] &, GroupGenerators[g]]]];
		as = Sort[a[[1]], (Length[#1] > Length[#2]) &];
		bs = Sort[b[[1]], (Length[#1] > Length[#2]) &];
		If[Map[Length, as] != Map[Length, bs], Throw[False]];

 		sc = GroupStabilizerChain[g, GroupActionBase -> Flatten[as]];
		basen = Position[sc, PermutationGroup[{}]][[1, 1]] - 1;
		sc = sc[[1 ;; basen + 1]];
		base = sc[[basen + 1, 1]];
		follow = Table[i > 1 && base[[i-1]]^a == base[[i]], {i, basen}];

		bcyclelen = Table[pos = Position[bs, set[[i]]]; If[pos == {}, 1, Length[bs[[pos[[1, 1]]]]]], {i, Length[set]}];

		cangoto = Table[
			pos = Position[as, base[[i]]];
			len = If[pos == {}, 1, Length[as[[pos[[1, 1]]]]]];
			Select[GroupOrbits[g, {base[[i]]}][[1]], (bcyclelen[[#]] == len)&]
		, {i, basen}];

		GroupConjugatesQBT[a, b, sc, base, cangoto, follow, {}]
	]
]

(* this is the public version, we check if a,b are elements of g and then call the inner version *)
GroupConjugatesQ[g_?GroupQ, a_Cycles, b_Cycles] :=
	If[!GroupElementQ[g, a],
		Message[GroupConjugatesQ::notelement, a, g];
		If[!GroupElementQ[g, b],
			Message[GroupConjugatesQ::notelement, b, g];
		];
	, (* else *)
		If[!GroupElementQ[g, b],
			Message[GroupConjugatesQ::notelement, b, g];
		, (* else *)
			GroupConjugatesQInner[g, a, b]
		]
	]

(* TODO *)
GroupConjugacyClassRepresentatives[g_?GroupQ] := GroupConjugacyClassRepresentatives[g] = Module[{ret, n, sum, x, k, cent, centorder},
	ret = {GroupIdentity[g]};
	sum = 1;
	k = 1;
	n = GroupOrder[g];
	x = GroupIdentity[g];
	cent = GroupCentralizer[g, x];
	centorder = GroupOrder[cent];
	While[sum < n,
	  	x = GroupElements[cent, {RandomInteger[{1, centorder}]}][[1]];
		cent = GroupCentralizer[g, x];
		centorder = GroupOrder[cent];
		Catch[
			Do[If[GroupConjugatesQ[g, ret[[i]], x], Throw[True]], {i, 1, k}];
			k = k+1;
			ret = Append[ret, x];
			sum = sum + n/centorder
		]
	];
	ret
]

(* we determine numbers of conjugacy classes by computing the representatives and count them, we only compute this once for every group *)
GroupNumOfConjugacyClasses[g_?GroupQ] := GroupNumOfConjugacyClasses[g] = Length[GroupConjugacyClassRepresentatives[g]]

(* TODO *)
GroupConjugacyClassSizes[g_?GroupQ] := GroupConjugacyClassSizes[g] = Module[{n},
	n = GroupOrder[g];
	Map[(n/GroupOrder[GroupCentralizer[g, #]])&, GroupConjugacyClassRepresentatives[g]]
]

(* size of a's conjugacy class = (G : C_G(a)) *)
GroupConjugacyClassSize[g_?GroupQ, a_] := GroupConjugacyClassSize[g, a] =
	If[!GroupElementQ[g, a],
		Message[GroupConjugacyClassSize::notelement, a, g];
	, (* else *)
		GroupOrder[g]/GroupOrder[GroupCentralizer[g, a]]
	]

(* we determine number of the conjugacy class of a specific element by computing representatives and then try if they are conjugates *)
GroupConjugacyClassNum[g_, a_] := Module[{repr},
	(* we calculate representatives *)
	repr = GroupConjugacyClassRepresentatives[g];
	(* we go through the elements *)
	Do[
		(* if a~repr[[i]] then we return i *)
		If[GroupConjugatesQ[g, a, repr[[i]]],
			Return[i]
		]
	, {i, Length[repr]}]
]

(* we determine number of class with previous function and return its representative element *)
GroupConjugacyClassRepresentative[g_, a_] := GroupConjugacyClassRepresentatives[g][[GroupConjugacyClassNum[g, a]]]

(* TODO *)
GroupConjugacyClassInverses[g_] := Map[GroupConjugacyClassNum[g, #^(-1)]&, GroupConjugacyClassRepresentatives[g]]

(* exponent is the least common multiplier of orders of the class representatives *)
GroupExponent[g_?GroupQ] := GroupExponent[g] = Apply[LCM, Map[GroupElementOrder[g, #]&, GroupConjugacyClassRepresentatives[g]]]

(* we search for the smallest prime with e|p-1 and p > 2*sqrt(|G|) *)
GroupCharacterTableDixonPrime[g_] := GroupCharacterTableDixonPrime[g] = Module[{p, e},
	e = GroupExponent[g];
	p = (Floor[(2*Floor[Sqrt[GroupOrder[g]]]-1)/e]+1)*e+1;
	While [!PrimeQ[p], p = p + e];
	p
]

(* TODO *)
GroupCharacterTableMTRow[g_, i_, k_] := GroupCharacterTableMTRow[g, i, k] = Module[{classes, iclass, kelem, x, j, p, ret},
	classes = GroupConjugacyClassRepresentatives[g];
	ret = ConstantArray[0, GroupNumOfConjugacyClasses[g]];
	If[i == 1, Return[ReplacePart[ret, k -> 1]]];
	p = GroupCharacterTableDixonPrime[g];
	If[k == 1, Return[ReplacePart[ret, GroupConjugacyClassNum[g, classes[[i]]^(-1)] -> Mod[GroupConjugacyClassSize[g, classes[[i]]], p]]]];
	classes = GroupConjugacyClassRepresentatives[g];
	iclass = classes[[i]]^g;
	kelem = classes[[k]];
	Do[
		j = GroupConjugacyClassNum[g, iclass[[x]]^(-1)**kelem];
		ret = ReplacePart[ret, j -> Mod[ret[[j]]+1, p]]
	, {x, Length[iclass]}];
	ret
]

(* we put all the rows together to form the M table *)
GroupCharacterTableMT[g_, i_] := Table[GroupCharacterTableMTRow[g, i, k], {k, 1, GroupNumOfConjugacyClasses[g]}]

(* TODO *)
GroupCharacterScalarProduct[g_, a_, b_] := Sum[a[[i]]*Conjugate[b[[i]]], {i, Length[a]}]/GroupOrder[g]

(* there is no internal Mathematica function which can compute intersection of two subspaces of a vector space, so we make a public one *)
SubspaceIntersection[a_, b_, opts___] := Module[{result},
	(* if one subspace is empty then the intersection is empty as well *)
	If[Length[a] == 0 || Length[b] == 0, Return[{}]];
	(* otherwise the intersection is the complementer subspace of their completementer's union *)
	result = NullSpace[Union[NullSpace[a, opts], NullSpace[b, opts]], opts];
	(* if result is empty we return *)
	If[Length[result] == 0, Return[{}]];
	(* otherwise we compute the echelonized base and return that *)
	RowReduce[result, opts]
]

(* we define Modulus option with 0 as default *)
Options[SubspaceIntersection] = {Modulus -> 0}

(* TODO *)
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

(* TODO *)
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

(* TODO *)
GroupCharacterTableNormalize[g_, a_] := Module[{h, p, s, inv, d, n, x},
	n = GroupOrder[g];
	h = GroupConjugacyClassSizes[g];
	p = GroupCharacterTableDixonPrime[g];
	inv = GroupConjugacyClassInverses[g];
	s = Sum[h[[i]]*a[[i]]*a[[inv[[i]]]], {i, Length[a]}];
	d = Min[Map[#[[1, 2]]&, Solve[n/x^2 == s, x, Modulus -> p]]];
	Mod[a*d, p]
]

(* TODO *)
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

(* TODO *)
GroupCharacterTable[g_?GroupQ] := GroupCharacterTable[g] = Module[{e, einv, r, p, t, s, i, j, k, l, repr, fin},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	e = GroupExponent[g];
	repr = GroupConjugacyClassRepresentatives[g];
	einv = PowerMod[e, -1, p];
	t = (-1)^(2/e);
	s = PowerMod[PrimitiveRoot[p], (p-1)/e, p];
	fin = GroupCharacterTableFinite[g];
	Table[
		Simplify[
			Sum[
				Mod[
					einv*Sum[
						fin[[i, GroupConjugacyClassNum[g, repr[[j]]^l]]]*PowerMod[s, -k*l, p]
					, {l, 0, e-1}]
				, p]*t^k
			, {k, 0, e-1}]
		, TimeConstraint -> 1]
	, {i, 1, r}, {j, 1, r}]
]

(* end of "GroupExt`Private`" *)
End[]

(* end of "GroupExt`" *)
EndPackage[]

