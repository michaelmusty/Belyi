s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "7T3-[3,3,3]-331-331-331-g0";
s`BelyiDBFilename := "7T3-[3,3,3]-331-331-331-g0.m";
s`BelyiDBDegree := 7;
s`BelyiDBOrders := \[ 3, 3, 3 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7 ]:
 Order := 21 > |
[ 1, 5, 2, 6, 3, 7, 4 ],
[ 3, 7, 4, 1, 5, 2, 6 ],
[ 4, 1, 5, 2, 6, 3, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<7 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<7 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<7 |  
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 3, 7, 4, 1, 5, 2, 6 ],
\[ 4, 1, 5, 2, 6, 3, 7 ]:
 Order := 21 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 3, 7, 4, 1, 5, 2, 6 ],
\[ 4, 1, 5, 2, 6, 3, 7 ]:
 Order := 21 >) |
[ PermutationGroup<7 |  
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 3, 7, 4, 1, 5, 2, 6 ],
\[ 4, 1, 5, 2, 6, 3, 7 ]:
 Order := 21 > |
[ 3, 7, 4, 1, 5, 2, 6 ],
[ 7, 4, 1, 5, 2, 6, 3 ],
[ 2, 6, 3, 7, 4, 1, 5 ]
],
[ PermutationGroup<7 |  
\[ 1, 5, 2, 6, 3, 7, 4 ],
\[ 3, 7, 4, 1, 5, 2, 6 ],
\[ 4, 1, 5, 2, 6, 3, 7 ]:
 Order := 21 > |
[ 4, 6, 1, 3, 5, 7, 2 ],
[ 3, 5, 7, 2, 4, 6, 1 ],
[ 1, 3, 5, 7, 2, 4, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7 ]:
 Order := 21 >) |
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7 ]:
 Order := 21 > |
[ 1, 5, 2, 6, 3, 7, 4 ],
[ 3, 7, 4, 1, 5, 2, 6 ],
[ 4, 1, 5, 2, 6, 3, 7 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 4, 6, 1, 3, 5, 7 ]:
 Order := 21 > |
[ 1, 3, 5, 7, 2, 4, 6 ],
[ 4, 6, 1, 3, 5, 7, 2 ],
[ 3, 5, 7, 2, 4, 6, 1 ]
]
];

/*
Base Field Data
*/

base_field_data := [* *];
K1<nu1> := NumberField(Polynomial([RationalField() | 1, 1, 1]));
place1 := InfinitePlaces(K1)[1];
conj1 := false;
CC<I> := ComplexField(20);
z1 := 0.00000000000000000000p20;
base_field_data_1 := [* K1, place1, conj1, z1 *];
Append(~base_field_data, base_field_data_1);
K2<nu2> := NumberField(Polynomial([RationalField() | 1, 1, 1]));
place2 := InfinitePlaces(K2)[1];
conj2 := true;
CC<I> := ComplexField(20);
z2 := 0.00000000000000000000p20;
base_field_data_2 := [* K2, place2, conj2, z2 *];
Append(~base_field_data, base_field_data_2);
s`BelyiDBBaseFieldData := base_field_data;

/*
Belyi Maps
*/

curves := [* *];
maps := [* *];
K := K1;
X1 := Curve(ProjectiveSpace(PolynomialRing(K1, 2)));
KX1<x> := FunctionField(X1);
phi1 := KX1!((-1/686*x^7 + 1/2*x^6 + 1/98*(-108*nu1 - 5139)*x^5 + 1/14*(4572*nu1 + 15867)*x^4 + 1/98*(-2794392*nu1 + 4834107)*x^3 + 1/98*(41394888*nu1 + 76952835)*x^2 + 1/98*(2242769796*nu1 + 2019357135)*x + 1/686*(91042624620*nu1 + 114639245001))/(x^6 + 1/7*(4572*nu1 + 15867)*x^4 + 1/49*(41394888*nu1 + 76952835)*x^2 + 1/343*(91042624620*nu1 + 114639245001)));
Append(~curves, X1);
Append(~maps, phi1);
K := K2;
X2 := Curve(ProjectiveSpace(PolynomialRing(K2, 2)));
KX2<x> := FunctionField(X2);
phi2 := KX2!((-1/686*x^7 + 1/2*x^6 + 1/98*(-108*nu2 - 5139)*x^5 + 1/14*(4572*nu2 + 15867)*x^4 + 1/98*(-2794392*nu2 + 4834107)*x^3 + 1/98*(41394888*nu2 + 76952835)*x^2 + 1/98*(2242769796*nu2 + 2019357135)*x + 1/686*(91042624620*nu2 + 114639245001))/(x^6 + 1/7*(4572*nu2 + 15867)*x^4 + 1/49*(41394888*nu2 + 76952835)*x^2 + 1/343*(91042624620*nu2 + 114639245001)));
Append(~curves, X2);
Append(~maps, phi2);
s`BelyiDBBelyiCurves := curves;
s`BelyiDBBelyiMaps := maps;

/*
Exact Data
*/


/*
Numerical Data
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
