BeginPackage["GroupExt`"]

(* list of public functions with usages *)
NullQ::usage = "NullQ[expr] gives True if expr is Null, and False otherwise."
GroupQ::usage = "GroupQ[expr] gives True if expr is a group, and False otherwise."
QuaternionGroup::usage = ""
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
GroupCharacterTableFinite::usage = ""
GroupCharacterTableDixonPrime::usage = ""
GroupCharacterScalarProduct::usage = ""
GroupElementFromImage::usage = ""
GroupElementFromImages::usage =

Begin["GroupExt`Private`"]

(* there is no proper way to determine if something is null *)
NullQ[x_] := ToString[x] == "Null" && !StringQ[x]

(* we only deal with permutation groups so identity element is always an empty cycle *)
GroupIdentity[g_?GroupQ] := Cycles[{}]

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

(* we declare the quaternion group *)
QuaternionGroup[] := PermutationGroup[{Cycles[{{1, 3, 2, 4}, {5, 8, 6, 7}}], Cycles[{{1, 5, 2, 6}, {3, 7, 4, 8}}]}]
GroupQ[g_QuaternionGroup] := True

(* in Mathematica 8.0.0 there is a bug that crashes GroupCentralizer[] if called with the identity element (fixed in 8.0.1) *)
Off[General::shdw]
GroupExt`GroupCentralizer[g_?GroupQ, x_Cycles] := If[GroupIdentity[g] == x, g, System`GroupCentralizer[g, x]]
On[General::shdw]


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
GroupElementOrder[g_?GroupQ, a_Cycles] := PermutationOrder[a]

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

(* We find conjugacy classes by testing random elements, each taken from the last element's centralizer *)
GroupConjugacyClassRepresentatives[g_?GroupQ] := GroupConjugacyClassRepresentatives[g] = Module[{repr, n, sum, x, k, cent, centorder},
	n = GroupOrder[g];
	(* at the beginning we only know the identity as a group representative *)
	(* at each step, we have a group element (x), calculate its centralizer (cent) and its order (centorder) *) 
	x = GroupIdentity[g];
	cent = g;
	centorder = n;
	(* we will store the representatives in repr *)
	repr = {x};
	(* k is the number of already found conjugacy classes *)
	k = 1;
	(* sum is the total number of elements in the known classes *)
	sum = 1;
	(* we are done when we find all elements, so we repeat until sum = n *)
	While[sum < n,
		(* we take 3 random elements before actually testing it *)
		Do[
			(* we get a random element from the last elements centralizer *)
	  		x = First[GroupElements[cent, {RandomInteger[{1, centorder}]}]];
			cent = GroupCentralizer[g, x];
			centorder = GroupOrder[cent];
		, {3}];
		Catch[
			(* we step out of the Catch[] block if x is in an already known conjugacy class *)
			Do[If[GroupConjugatesQ[g, repr[[i]], x], Throw[True]], {i, 1, k}];
			(* if we are here, we found a new class *)
			k = k+1;
			repr = Append[repr, x];
			sum = sum + n/centorder
		]
	];
	repr
]

(* we determine numbers of conjugacy classes by computing the representatives and counting them *)
GroupNumOfConjugacyClasses[g_?GroupQ] := GroupNumOfConjugacyClasses[g] = Length[GroupConjugacyClassRepresentatives[g]]

(* we compute |G : C_G(a)| for all representatives and return them in a list *)
GroupConjugacyClassSizes[g_?GroupQ] := GroupConjugacyClassSizes[g] = Module[{n},
	n = GroupOrder[g];
	Map[(n/GroupOrder[GroupCentralizer[g, #]])&, GroupConjugacyClassRepresentatives[g]]
]

(* size of a's conjugacy class = |G : C_G(a)| *)
GroupConjugacyClassSize[g_?GroupQ, a_Cycles] :=
	If[!GroupElementQ[g, a],
		Message[GroupConjugacyClassSize::notelement, a, g];
	, (* else *)
		GroupOrder[g]/GroupOrder[GroupCentralizer[g, a]]
	]

(* we determine number of the conjugacy class of a specific element by computing representatives and then try if they are conjugates *)
GroupConjugacyClassNum[g_?GroupQ, a_Cycles] := Module[{repr},
	(* we calculate representatives *)
	repr = GroupConjugacyClassRepresentatives[g];
	Catch[
		(* we iterate over them *)
		Do[
			(* if a~repr[[i]] then we return i *)
			If[GroupConjugatesQ[g, a, repr[[i]]], Throw[i]]
		, {i, Length[repr]}];
		(* if we didn't found it then a is not in g *)
		Message[GroupConjugacyClassNum::notelement, a, g]
	]
]

(* we determine number of class with previous function and return its representative element *)
GroupConjugacyClassRepresentative[g_?GroupQ, a_Cycles] := GroupConjugacyClassRepresentatives[g][[GroupConjugacyClassNum[g, a]]]

(* we compute indices of the conjugacy classes' inverses *)
GroupConjugacyClassInverses[g_?GroupQ] := GroupConjugacyClassInverses[g] = Map[GroupConjugacyClassNum[g, #^(-1)]&, GroupConjugacyClassRepresentatives[g]]

(* exponent is the least common multiplier of orders of the class representatives *)
GroupExponent[g_?GroupQ] := GroupExponent[g] = Apply[LCM, Map[GroupElementOrder[g, #]&, GroupConjugacyClassRepresentatives[g]]]

(* we search for the smallest prime with e|p-1 and p > 2*sqrt(|G|) *)
GroupCharacterTableDixonPrime[g_?GroupQ] := GroupCharacterTableDixonPrime[g] = Module[{p, e},
	(* e is the exponent *)
	e = GroupExponent[g];
	(* p is the first number that e|p-1 and p > 2*sqrt(|G|) *)
	p = (Floor[(2*Floor[Sqrt[GroupOrder[g]]]-1)/e]+1)*e+1;
	(* while p is not a prime, we increase it by e *)
	While [!PrimeQ[p], p = p + e];
	p
]

(* MT_i(k, j) = $|\{(a,b) \in G_1 \times G_2 \mid a \in C_i, b \in C_j, a*b=g_k\}|$  *)
GroupMTTableRow[g_, i_, k_] := GroupMTTableRow[g, i, k] = Module[{repr, inv, iclass, kelem, x, j, p, ret},
	repr = GroupConjugacyClassRepresentatives[g];
	inv = GroupConjugacyClassInverses[g];
	ret = ConstantArray[0, Length[repr]];
	If[i == 1, Return[ReplacePart[ret, k -> 1]]];
	p = GroupCharacterTableDixonPrime[g];
	If[k == 1, Return[ReplacePart[ret, inv[[i]] -> Mod[GroupConjugacyClassSize[g, repr[[i]]], p]]]];
	iclass = repr[[i]]^g;
	kelem = repr[[k]];
	Do[
		j = GroupConjugacyClassNum[g, iclass[[x]]^(-1)**kelem];
		ret = ReplacePart[ret, j -> Mod[ret[[j]]+1, p]]
	, {x, Length[iclass]}];
	ret
]

(* we put all the rows together to form the MT table *)
GroupMTTable[g_, i_] := GroupMTTable[g, i] = Table[GroupMTTableRow[g, i, k], {k, 1, GroupNumOfConjugacyClasses[g]}]

(* we calculate scalar product as 1/|G|\sum_{g \in G}a(g)b(g^-1) and not using conjugates as in the definition, because it works with finite fields as well *)
Options[GroupCharacterScalarProduct] = {Modulus -> 0}
GroupCharacterScalarProduct[g_?GroupQ, a_, b_, OptionsPattern[]] := Module[{sizes, inv, mod, ret},
	sizes = GroupConjugacyClassSizes[g];
	inv = GroupConjugacyClassInverses[g];
	mod = OptionValue[Modulus];
	ret = Sum[sizes[[i]]*a[[i]]*b[[inv[[i]]]], {i, Length[sizes]}];
	If[mod != 0, Mod[ret*PowerMod[GroupOrder[g], -1, mod], mod], ret/GroupOrder[g]]
]

(* there is no internal Mathematica function which can compute intersection of two subspaces of a vector space, so we make a public one *)
(* we define Modulus option with 0 as default *)
Options[SubspaceIntersection] = {Modulus -> 0}
SubspaceIntersection[a_, b_, OptionsPattern[]] := Module[{result, mod},
	(* if one subspace is empty then the intersection is empty as well *)
	If[Length[a] == 0 || Length[b] == 0, Return[{}]];
	mod = OptionValue[Modulus];
	(* otherwise the intersection is the complementer subspace of their complementer's union *)
	result = NullSpace[Union[NullSpace[a, Modulus -> mod], NullSpace[b, Modulus -> mod]], Modulus -> mod];
	(* if result is empty we return *)
	If[Length[result] == 0, Return[{}]];
	(* otherwise we compute the echelonized base and return that *)
	RowReduce[result, Modulus -> mod]
]

(* TODO *)
GroupCharacterTableSplit[g_, i_, v_] := Module[{r, p, x, m, id, w, j},
	If[Length[v] == 1, Return[{v}]];
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	m = GroupMTTable[g, i];
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
GroupCharacterTableFinite[g_?GroupQ] := GroupCharacterTableFinite[g] = Module[{x, r, i, p},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	If[r == 1, Return[{{1}}]];
	x = {IdentityMatrix[r]};
	Do[
		x = Apply[Union, Map[GroupCharacterTableSplit[g, i, #]&, x]]
	, {i, 2, r}];
	Sort[Map[
		(* we have to multiply each eigenvector with a constant such that their norms becomes 1 *)
		Mod[#*PowerMod[GroupCharacterScalarProduct[g, #, #, Modulus -> p], -1/2, p], p]&,
		Table[x[[i, 1]], {i, r}]
	]]
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
		Sum[
			Mod[
				einv*Sum[
					fin[[i, GroupConjugacyClassNum[g, repr[[j]]^l]]]*PowerMod[s, -k*l, p]
				, {l, 0, e-1}]
			, p]*t^k
		, {k, 0, e-1}]
	, {i, 1, r}, {j, 1, r}]
]

End[]
EndPackage[]
