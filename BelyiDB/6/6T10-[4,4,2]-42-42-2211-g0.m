s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "6T10-[4,4,2]-42-42-2211-g0";
s`BelyiDBFilename := "6T10-[4,4,2]-42-42-2211-g0.m";
s`BelyiDBDegree := 6;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 6, 1, 2, 5, 4, 3 ],
[ 3, 4, 1, 2, 5, 6 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<6 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<6 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<6 |  
\[ 4, 1, 6, 5, 2, 3 ],
\[ 6, 1, 2, 5, 4, 3 ],
\[ 3, 4, 1, 2, 5, 6 ]:
 Order := 36 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 4, 1, 6, 5, 2, 3 ],
\[ 6, 1, 2, 5, 4, 3 ],
\[ 3, 4, 1, 2, 5, 6 ]:
 Order := 36 >) |
[ PermutationGroup<6 |  
\[ 4, 1, 6, 5, 2, 3 ],
\[ 6, 1, 2, 5, 4, 3 ],
\[ 3, 4, 1, 2, 5, 6 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 6, 1, 2, 5, 4, 3 ],
[ 3, 4, 1, 2, 5, 6 ]
],
[ PermutationGroup<6 |  
\[ 4, 1, 6, 5, 2, 3 ],
\[ 6, 1, 2, 5, 4, 3 ],
\[ 3, 4, 1, 2, 5, 6 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 6, 3, 2, 1, 4, 5 ],
[ 3, 6, 1, 4, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 >) |
[ PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 6, 1, 2, 5, 4, 3 ],
[ 3, 4, 1, 2, 5, 6 ]
],
[ PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 2, 5, 4, 3, 6, 1 ],
[ 1, 2, 5, 6, 3, 4 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 >)) |
[ PowerSequence(PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 >) |
[ PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 6, 1, 2, 5, 4, 3 ],
[ 3, 4, 1, 2, 5, 6 ]
],
[ PermutationGroup<6 |  
\[ 1, 4, 3, 6, 5, 2 ],
\[ 5, 4, 3, 2, 1, 6 ],
\[ 4, 1, 6, 5, 2, 3 ]:
 Order := 36 > |
[ 4, 1, 6, 5, 2, 3 ],
[ 2, 5, 4, 3, 6, 1 ],
[ 1, 2, 5, 6, 3, 4 ]
]
]
];

/*
Base Field Data
*/

base_field_data := [* *];
K1<nu1> := NumberField(Polynomial([RationalField() | -3, 0, 1]));
place1 := InfinitePlaces(K1)[1];
conj1 := false;
CC<I> := ComplexField(20);
z1 := 0.00000000000000000000p20;
base_field_data_1 := [* K1, place1, conj1, z1 *];
Append(~base_field_data, base_field_data_1);
K2<nu2> := NumberField(Polynomial([RationalField() | -3, 0, 1]));
place2 := InfinitePlaces(K2)[2];
conj2 := false;
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
phi1 := KX1!((x^6 - 2*x^5 + x^4)/(x^6 - 2*x^5 + x^4 + 1/9*(2*nu1 + 3)*x^2 + 1/27*(-8*nu1 - 14)*x + 1/243*(26*nu1 + 45)));
Append(~curves, X1);
Append(~maps, phi1);
K := K2;
X2 := Curve(ProjectiveSpace(PolynomialRing(K2, 2)));
KX2<x> := FunctionField(X2);
phi2 := KX2!((x^6 - 2*x^5 + x^4)/(x^6 - 2*x^5 + x^4 + 1/9*(2*nu2 + 3)*x^2 + 1/27*(-8*nu2 - 14)*x + 1/243*(26*nu2 + 45)));
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
