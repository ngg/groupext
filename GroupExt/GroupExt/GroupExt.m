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
GroupConjugacyClassInverses::usage = ""
GroupConjugacyClassNum::usage = ""
GroupConjugacyClass::usage = ""
GroupConjugacyClassOf::usage = ""
GroupCharacterTable::usage = ""
GroupCharacterTableFinite::usage = ""
GroupCharacterTableDixonPrime::usage = ""
GroupCharacterScalarProduct::usage = ""
GroupElementFromImage::usage = ""
GroupElementFromImages::usage = ""
GroupIrredundantStabilizerChain::usage = ""

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
SetAttributes[Power, Protected]

(* for speed reasons, we don't check if a is in g or not *)
GroupElementOrder[g_?GroupQ, a_Cycles] := PermutationOrder[a]

(* breadth-first-search for an element that moves a to b *)
GroupElementFromImage[g_?GroupQ, a_Integer, b_Integer] := Module[{lk = 1, list, c, x, i},
	Catch[
		(* if a == b then the identity is good *)
		If[a == b, Throw[GroupIdentity[g]]];
		s = GroupGenerators[g];
		(* we start bfs from the identity which moves a to a *)
		list = {GroupIdentity[g] -> a};
		lk = 1;
		(* while we have new elements where we can move a to *)
		While[lk <= Length[list],
			(* we try every generator *)
			Do[
				(* we compute the new group element (c), and where that moves a to (x) *)
	 			c = list[[lk, 1]]**s[[i]];
				x = list[[lk, 2]]^s[[i]];
				(* if it moves a to b then we're done *)
				If[x == b, Throw[c]];
				(* if we couldn't get to x yet then we add c->x to our list *)
				If[Count[list, x, 2] == 0, list = Append[list, c -> x]]
			, {i, Length[s]}];
			lk = lk + 1
		];
		(* if we can't get to b then we return Null *)
		Null
	]
]

(* the builtin GroupStabilizerChain can give redundant base *)
GroupIrredundantStabilizerChain[g_?GroupQ, opts:OptionsPattern[GroupStabilizerChain]] := Module[{sc, ret, i},
	(* first we call the original version *)
	sc = GroupStabilizerChain[g, opts];
	(* the first element is always necessary *)
	ret = {First[sc]};
	Do[
		(* we add an element if the group is not the same as the previously added, and we only add the last base element to the list *) 
		If[ret[[-1, 2, 1]] != sc[[i, 2, 1]], ret = Append[ret, Append[ret[[-1, 1]], sc[[i, 1, -1]]] -> sc[[i, 2]]]]
	, {i, 2, Length[sc]}];
	ret
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
		, {i, basen}];
		ret
	]
]

(* TODO *)
GroupElementFromImages[g_?GroupQ, s_] := Module[{sc, wantedbase, base, basen, ret, i, x},
	Catch[
		wantedbase = Map[First, s];
		sc = GroupIrredundantStabilizerChain[g, GroupActionBase -> wantedbase];
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
				, {i, Length[cangoto[[imgn+1]]]}];
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

 		sc = GroupIrredundantStabilizerChain[g, GroupActionBase -> Flatten[as]];
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

(* breadth-first-search for elements in the k-th conjugacy class *)
GroupConjugacyClass[g_?GroupQ, k_Integer] := GroupConjugacyClass[g, k] = Module[{list, i, next, s},
	(* we calculate the generators *)
	s = GroupGenerators[g];
	(* list contains found elements *)
	list = {GroupConjugacyClassRepresentatives[g][[k]]};
	(* next-th element of the list is coming *)
	next = 1;
	(* we go through the elements of the list *)
	While[next <= Length[list],
		Do[
			(* x is the new element we get by conjugating the next-th element with the i-th generator *)
			x = list[[next]]^s[[i]];
			(* if we haven't found x yet then we add it to the list *)
			If[Count[list, x] == 0, list = Append[list, x]]
		, {i, Length[s]}];
		next = next+1
	];
	list
]

(* this function is self-explanatory *)
GroupConjugacyClassOf[g_?GroupQ, a_Cycles] := GroupConjugacyClass[g, GroupConjugacyClassNum[g, a]]

(* we determine number of class with previous function and return its representative element *)
GroupConjugacyClassRepresentative[g_?GroupQ, a_Cycles] := GroupConjugacyClassRepresentatives[g][[GroupConjugacyClassNum[g, a]]]

(* we compute indices of the conjugacy classes' inverses *)
GroupConjugacyClassInverses[g_?GroupQ] := GroupConjugacyClassInverses[g] = Map[GroupConjugacyClassNum[g, #^(-1)]&, GroupConjugacyClassRepresentatives[g]]

(* exponent is the least common multiplier of orders of the class representatives *)
GroupExponent[g_?GroupQ] := GroupExponent[g] = Apply[LCM, Map[GroupElementOrder[g, #]&, GroupConjugacyClassRepresentatives[g]]]

(* MT_i(k, j) = $|\{(a,b) \in G_1 \times G_2 \mid a \in C_i, b \in C_j, a*b=g_k\}|$  *)
GroupMTTableRow[g_, i_, k_] := GroupMTTableRow[g, i, k] = Module[{repr, inv, ret, iclass, j, l},
	(* we calculate the representatives and inverses *)
	repr = GroupConjugacyClassRepresentatives[g];
	inv = GroupConjugacyClassInverses[g];
	(* we will return a Length[repr] long array, initially it's all zero *)
	ret = ConstantArray[0, Length[repr]];
	(* if i == 1 then MT_i is the identity matrix, so in its kth row there is only one non-zero element, the kth *) 
	If[i == 1, Return[ReplacePart[ret, k -> 1]]];
	(* the first row always has only one non-zero element, the inv[[i]]-th element is the size of its conjugacy class *)
	If[k == 1, Return[ReplacePart[ret, inv[[i]] -> GroupConjugacyClassSizes[g][[i]]]]];
	(* otherwise we compute an element from the kth class and iterate through the ith class *)
	iclass = GroupConjugacyClass[g, i];
	Do[
		j = GroupConjugacyClassNum[g, iclass[[l]]^(-1)**repr[[k]]];
		(* we increase the j-th element by 1 *)
		ret = ReplacePart[ret, j -> ret[[j]]+1]	
	, {l, Length[iclass]}];
	ret
]

(* we calculate scalar product as 1/|G|\sum_{g \in G}a(g)b(g^-1) and not using conjugates as in the definition, because it works with finite fields as well *)
Options[GroupCharacterScalarProduct] = {Modulus -> 0}
GroupCharacterScalarProduct[g_?GroupQ, a_, b_, OptionsPattern[]] := Module[{sizes, inv, mod, ret},
	sizes = GroupConjugacyClassSizes[g];
	inv = GroupConjugacyClassInverses[g];
	mod = OptionValue[Modulus];
	(* we calculate the sum *)
	ret = Sum[sizes[[i]]*a[[i]]*b[[inv[[i]]]], {i, Length[sizes]}];
	(* we have to divide it by GroupOrder[g] *)
	If[mod != 0, Mod[ret*PowerMod[GroupOrder[g], -1, mod], mod], ret/GroupOrder[g]]
]

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

(* we try to split V into direct sum of smaller subspaces based on GroupMTTable[g, i] *)
GroupCharacterTableSplit[g_, i_, V_] := Module[{r, p, x, Mp, bp, id, j, s, iinv, A, c, im, eigenvalues, lin},
	s = Length[V];
	(* if V is 1-dimensional, we cannot split it *)
	If[s == 1, Return[{V}]];
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	iinv = GroupConjugacyClassInverses[g][[i]];
	(* if all basevectors but the first has 0 at position iinv, then we cannot split *)
	If[Count[Map[#[[iinv]]&, Rest[V]], 0] == Length[V]-1, Return[{V}]];
	(* we compute the place of leading non-zero elements of the basevectors *)
	c = Map[Position[#, Except[0], 1, Heads -> False][[1, 1]]&, V];
	(* and the basevectors at c places *)
	bp = Table[Map[V[[j, #]]&, c], {j, s}];
	(* we need these rows of MT *)
	Mp = Mod[Map[GroupMTTableRow[g, i, #]&, c], p];
	(* we construct an A matrix such that MT.V^T = V^T.A where MT is GroupMTTable[g, i] *)  
	A = Transpose[Map[Function[{b},
		(* first we compute the image of the basevector, but only the values at the c places *)
		im = Mod[b.Transpose[Mp], p];
		(* next we want to have im as linear combination of basevectors *)
		lin = {};
		(* we do something like Gauss-elimination to get the coefficients (it works because V is a row-reduced base) *)
		Do[
			lin = Append[lin, im[[j]]];
			im = Mod[im-im[[j]]*bp[[j]], p]
		, {j, s}];
		lin
	], V]];
	(* we find A's eigenvalues *)
	eigenvalues = Map[#[[1,2]]&, Union[Solve[CharacteristicPolynomial[A, x] == 0, x, Modulus -> p]]];
	(* for each eigenvalue we find its eigenspace, and calculate its generators in the normal coordinate system *)
	id = IdentityMatrix[s];
	Select[Map[RowReduce[NullSpace[A - #*id, Modulus -> p].V, Modulus -> p]&, eigenvalues], (Length[#] > 0)&]
]

(* we determine the character table over F_p by figuring out the common eigenvectors of the MT matrices *)
GroupCharacterTableFinite[g_?GroupQ] := GroupCharacterTableFinite[g] = Module[{subspaces, r, i, p},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	(* initially we have the whole vectorspace as the single subspace *)
	subspaces = {IdentityMatrix[r]};
	(* we split subspaces into direct sums until each is 1-dimensional *)
	Do[
		subspaces = Apply[Union, Map[GroupCharacterTableSplit[g, i, #]&, subspaces]]
	, {i, 2, r}];
	(* we calculate the characters from the eigenvectors and then sort them *)
	Sort[Map[
		(* we have to multiply each eigenvector with a constant such that their norms becomes 1 *)
		Mod[#*PowerMod[GroupCharacterScalarProduct[g, #, #, Modulus -> p], -1/2, p], p]&,
		Table[subspaces[[i, 1]], {i, r}]
	]]
]

(* we use the finite table to compute the normal one *)
GroupCharacterTable[g_?GroupQ] := GroupCharacterTable[g] = Module[{e, einv, r, p, t, s, i, j, k, l, repr, fin, reprl, inv, skip, row},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupCharacterTableDixonPrime[g];
	e = GroupExponent[g];
	repr = GroupConjugacyClassRepresentatives[g];
	inv = GroupConjugacyClassInverses[g];
	(* we compute the finite version first *)
	fin = GroupCharacterTableFinite[g];
	(* we can skip computation of those columns whose inverses' column is already computed, because we can conjugate those *)
	skip = Table[inv[[i]] < i, {i, r}];
	(* t is a complex e-th root of unity *)
	t = (-1)^(2/e);
	(* s is an element which has order e in F_p *)
	s = PowerMod[PrimitiveRoot[p], (p-1)/e, p];
	(* we precompute some expressions that will be used a lot *)
	reprl = Table[GroupConjugacyClassNum[g, repr[[j]]^k], {j, r}, {k, e}];
	einv = PowerMod[e, -1, p];
	(* we finally compute the character table, and then try to simplify the result for at most 10 seconds *)
	FullSimplify[Table[
		row = {};
		Do[
			(* we write the elements of the character table as a polynomial of t, row contains the coefficients *)
			(* we can compute them with this sum (or we reverse the coefficients of the inverse column for conjugation) *)
			row = Append[row, If[skip[[j]], RotateLeft[Reverse[row[[inv[[j]]]]]], Table[Mod[einv*Sum[fin[[i, reprl[[j, l]]]]*PowerMod[s, -k*l, p], {l, e}], p], {k, e}]]]
		, {j, r}];
		(* now we sum it *)
		Table[Sum[row[[j, k]]*t^k, {k, e}], {j, r}]
	, {i, r}], TimeConstraint -> 10]
]

End[]
EndPackage[]
