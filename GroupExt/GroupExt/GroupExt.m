BeginPackage["GroupExt`"]

(* list of public functions with usages *)
NullQ::usage = "NullQ[expr] gives True if expr is Null, and False otherwise."
GroupQ::usage = "GroupQ[expr] gives True if expr is a group, and False otherwise."
GroupActionSetSort::usage = "GroupActionSetSort[actset] sorts the elements of actset into an order in which elements of option GroupActionBase are the first ones and then other elements follow."
CyclesActionSet::usage = "CyclesActionSet[elem] gives the action set of a group element."
GroupActionSet::usage = "GroupActionSet[group] gives the action set of a group."
GroupExponent::usage = "GroupExponent[group] gives the exponent of the group."
GroupElementFromImage::usage = "GroupElementFromImage[group, a, b] gives an element of the group which moves a to b, or Null if there is no such element."
GroupIrredundantStabilizerChain::usage = "GroupIrredundantStabilizerChain[group] gives a stabilizer chain of the group according to the option GroupActionBase, but skips redundant base elements."
GroupConjugatesQ::usage = "GroupConjugatesQ[group, elem1, elem2] gives True if elem1 and elem2 are conjugates in the group, and False otherwise."
GroupConjugacyClassRepresentatives::usage = "GroupConjugacyClassRepresentatives[group] gives a list of group elements which represent the conjugacy classes."
GroupNumOfConjugacyClasses::usage = "GroupNumOfConjugacyClasses[group] gives the number of conjugacy classes in the group."
GroupConjugacyClassSizes::usage = "GroupConjugacyClassSizes[group] gives the list of sizes of the conjugacy classes (in the same order as GroupConjugacyClassRepresentatives[group] gives the elements."
GroupConjugacyClassInverses::usage = "GroupConjugacyClassInverses[group] gives the list whose k-th element is the index of the conjugacy class in which the inverses of the elements of the k-th conjugacy class are."
GroupConjugacyClassNum::usage = "GroupConjugacyClassNum[group, elem] gives the index of the conjugacy class of elem in group."
GroupConjugacyClass::usage = "GroupConjugacyClass[group, n] gives the full list of elements in the n-th conjugacy class."
GroupCharacterScalarProduct::usage = "GroupCharacterScalarProduct[group, chi, psi] gives the scalar product of two characters (chi and psi) of the group given by a list of values in the conjugacy classes."
GroupDixonPrime::usage = "GroupDixonPrime[group] gives the smallest prime number (p) such that GF[p] can be used to represent all the complex characters in."
GroupCharacterTableOverFiniteField::usage = "GroupCharacterTableOverFiniteField[group] gives the character table of the group over GF[p] where p is given by GroupDixonPrime[group]."
GroupCharacterTable::usage = "GroupCharacterTable[group] gives the character table of the group."

Begin["GroupExt`Private`"]

(* there is no proper way to determine if something is null *)
NullQ[x_] := ToString[x] == "Null" && !StringQ[x]

(* only way to check if something is a group is with a list like this *)
GroupQ[g_] := MemberQ[{
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

(* in Mathematica 8.0.0 there is a bug that crashes GroupCentralizer[] if called with the identity element (fixed in 8.0.1) *)
Off[General::shdw]
GroupExt`GroupCentralizer[g_?GroupQ, x_Cycles] := If[Cycles[{}] == x, g, System`GroupCentralizer[g, x]]
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

(* it can sort a subset of the group's action set by a base *)  
Options[GroupActionSetSort] = {GroupActionBase -> {}}
GroupActionSetSort[actset_List, OptionsPattern[]] := Module[{base},
	base = OptionValue[GroupActionBase];
	Join[Sort[Intersection[actset, base], (Position[base, #1][[1,1]] < Position[base, #2][[1,1]])&], Sort[Complement[actset, base]]]
] 

(* it gives the set a groupelement acts on (listable) *)
CyclesActionSet[a_Cycles, opts:OptionsPattern[GroupActionSetSort]] := GroupActionSetSort[Flatten[a[[1]]], opts]
SetAttributes[CyclesActionSet, Listable]

(* it gives the set the group acts on *)
GroupActionSet[g_?GroupQ, opts:OptionsPattern[GroupActionSetSort]] := GroupActionSetSort[Apply[Union, CyclesActionSet[GroupGenerators[g]]], opts]

(* exponent is the least common multiplier of orders of the class representatives *)
GroupExponent[g_?GroupQ] := GroupExponent[g] = Apply[LCM, Map[PermutationOrder, GroupConjugacyClassRepresentatives[g]]]

(* breadth-first-search for an element that moves a to b *)
GroupElementFromImage[g_?GroupQ, a_Integer, b_Integer] := Module[{lk = 1, list, c, x, i},
	Catch[
		(* if a == b then the identity is good *)
		If[a == b, Throw[Cycles[{}]]];
		s = GroupGenerators[g];
		(* we start bfs from the identity which moves a to a *)
		list = {Cycles[{}] -> a};
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

(* private function: Sifting procedure to get an element from some base images *)
GroupElementFromBaseImages[sc_, base_, img_, imgn_] := Module[{i, x, ret},
	Catch[
		(* we start with the identity *)
		ret = Cycles[{}];
		(* we iterate through given images *)
		Do[
			(* we look for an element that stabilizes the first i-1 base elements but moves base[[i]] to img[[i]]^(ret^(-1)) (this way x**ret moves base[[i]] to img[[i]] *)
			x = GroupElementFromImage[sc[[i,2]], base[[i]], img[[i]]^(ret^(-1))];
			(* if there are no such elemet then we return Null *)
			If[NullQ[x], Throw[Null]];
			(* we continue with x**ret *)
			ret = x**ret
		, {i, imgn}];
		(* if we are done with all the given images then ret is good *)
		ret
	]
]

(* we use a backtrack method to check if a and b are conjugates *)
GroupConjugatesQ[g_?GroupQ, a_Cycles, b_Cycles] := Module[{acycles, bcycles, sc, base, pos, p, borbitfirst}, Catch[
	(* we sort the cycles of a and b by length *)
	acycles = Sort[a[[1]], (Length[#1] > Length[#2]) &];
	bcycles = Sort[b[[1]], (Length[#1] > Length[#2]) &];
	(* if a and b has cycles of different length then they are not conjugates *)
	If[Map[Length, acycles] != Map[Length, bcycles], Throw[False]];
	(* we compute the stabilizer chain with a base in which elements of a's cycles  *)
	sc = GroupIrredundantStabilizerChain[g, GroupActionBase -> Flatten[acycles]];
	(* we compute its base *)
	base = sc[[-1, 1]];
	(* we compute positions of base elements in a, {x, y, z} means it's the y-th in the x-th cycle (which is z long); {0, 0, 1} means it's stabilized by a *)
	pos = Map[(p = Position[a, #, {3}]; If[Length[p] == 0, {0, 0, 1}, {p[[1, 2]], p[[1, 3]], Length[a[[1, p[[1, 2]]]]]}])&, base];
	(* we compute <b>'s orbits' first elements *)
	borbitfirst = Union[Complement[GroupActionSet[g], Flatten[b[[1]]]], Map[First[GroupActionSetSort[#, GroupActionBase -> base]]&, b[[1]]]];
	(* we call our backtrack function with initially no base images *)
	GroupConjugatesQBT[a, b, sc, base, Length[base], {}, 0, pos, borbitfirst]
]]

(* private function: the backtrack function *)
GroupConjugatesQBT[a_, b_, sc_, base_, basen_, img_, imgn_, pos_, borbitfirst_] := Module[{try, elem, l, p}, Catch[
	(* elem is an element whose base images start with img *)
	elem = GroupElementFromBaseImages[sc, base, img, imgn];
	(* if we have all the images then we check if it's good *)
	If[imgn == basen, Throw[a^elem == b]];
	(* l is the next base element's number *)
	l = imgn+1;
	(* try will be the list of possible images for the next base element *)
	(* if base[[l]] is in the same cycle in a as base[[imgn]] then we know the next image *)
	If[imgn > 0 && pos[[l, 1]] > 0 && pos[[l, 1]] == pos[[imgn, 1]],
		p = Position[b, img[[imgn]], {3}];
		try = {b[[1, p[[1, 2]], Mod[pos[[l, 2]]-pos[[imgn, 2]]+p[[1, 3]]-1, pos[[l, 3]]]+1]]}
	, (* else *)
		(* the elements whose images start with img are a coset of sc[[imgn+1, 2]] and elem is one of them, so these are the possible images for base[[imgn+1]] *)
		try = (base[[l]]^sc[[l, 2]])^elem;
		(* if base[[l]] is stabilized by a then img[[l]] must be stabilized by b *)
		If[pos[[l, 1]] == 0,
			try = Select[try, (Count[b, #, {3}] == 0)&]
		, (* else *)
			(* otherwise cycle-length must be the same *)
			try = Select[try, (p = Position[b, #, {3}]; Length[p] > 0 && Length[b[[1, p[[1, 2]]]]] == pos[[l, 3]])&]
		];
		(* if b stabilizer all images thus far (if borbitfirst != {}) then we only have to check <b>'s orbits' first element *)
		If[Length[borbitfirst] > 0, try = Intersection[try, borbitfirst]];
	];
	(* we try every possible image for base[[l]] *)
	Do[
		(* if it's good then we return True *)
		If[GroupConjugatesQBT[a, b, sc, base, basen, Append[img, try[[i]]], l, pos, If[Count[b, try[[i]], {3}] == 0, borbitfirst, {}]], Throw[True]]
	, {i, Length[try]}];
	(* if we didn't return True then it's False *)
	False
]]

(* We find conjugacy classes by testing random elements, each taken from the last element's centralizer *)
GroupConjugacyClassRepresentatives[g_?GroupQ] := GroupConjugacyClassRepresentatives[g] = Module[{repr, n, sum, x, k, cent, centorder},
	n = GroupOrder[g];
	(* at the beginning we only know the identity as a group representative *)
	(* at each step, we have a group element (x), calculate its centralizer (cent) and its order (centorder) *) 
	x = Cycles[{}];
	cent = g;
	centorder = n;
	(* we will store the representatives in repr *)
	repr = {x};
	(* k is the number of already found conjugacy classes *)
	k = 1;
	(* sum is the total number of elements in the known classes *)
	sum = 1;
	(* we are done when we find all elements, so we repeat until sum == n *)
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

(* we compute indices of the conjugacy classes' inverses *)
GroupConjugacyClassInverses[g_?GroupQ] := GroupConjugacyClassInverses[g] = Map[GroupConjugacyClassNum[g, #^(-1)]&, GroupConjugacyClassRepresentatives[g]]

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
		Null
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

(* private function: MT_i(k, j) = $|\{(a,b) \in G_1 \times G_2 \mid a \in C_i, b \in C_j, a*b=g_k\}|$  *)
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
GroupDixonPrime[g_?GroupQ] := GroupDixonPrime[g] = Module[{p, e},
	(* e is the exponent *)
	e = GroupExponent[g];
	(* p is the first number that e|p-1 and p > 2*sqrt(|G|) *)
	p = (Floor[(2*Floor[Sqrt[GroupOrder[g]]]-1)/e]+1)*e+1;
	(* while p is not a prime, we increase it by e *)
	While [!PrimeQ[p], p = p + e];
	p
]

(* private function: we try to split V into direct sum of smaller subspaces based on GroupMTTable[g, i] *)
GroupCharacterTableSplit[g_, i_, V_] := Module[{r, p, x, Mp, bp, id, j, s, iinv, A, c, im, eigenvalues, lin},
	s = Length[V];
	(* if V is 1-dimensional, we cannot split it *)
	If[s == 1, Return[{V}]];
	r = GroupNumOfConjugacyClasses[g];
	p = GroupDixonPrime[g];
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
GroupCharacterTableOverFiniteField[g_?GroupQ] := GroupCharacterTableOverFiniteField[g] = Module[{subspaces, r, i, p},
	r = GroupNumOfConjugacyClasses[g];
	p = GroupDixonPrime[g];
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
	p = GroupDixonPrime[g];
	e = GroupExponent[g];
	repr = GroupConjugacyClassRepresentatives[g];
	inv = GroupConjugacyClassInverses[g];
	(* we compute the finite version first *)
	fin = GroupCharacterTableOverFiniteField[g];
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
