s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T13-[6,3,2]-62-3311-2222-g0";
s`BelyiDBFilename := "8T13-[6,3,2]-62-3311-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 3, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ]:
 Order := 24 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 2, 8, 7, 5, 4, 6, 1 ],
[ 4, 7, 6, 1, 8, 3, 2, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 2, 8, 7, 5, 4, 6, 1 ],
\[ 4, 7, 6, 1, 8, 3, 2, 5 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 2, 8, 7, 5, 4, 6, 1 ],
\[ 4, 7, 6, 1, 8, 3, 2, 5 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 8, 2, 1, 6 ],
\[ 3, 2, 8, 7, 5, 4, 6, 1 ],
\[ 4, 7, 6, 1, 8, 3, 2, 5 ]:
 Order := 24 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 2, 8, 7, 5, 4, 6, 1 ],
[ 4, 7, 6, 1, 8, 3, 2, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 8, 3, 2, 5, 4, 7, 6, 1 ],
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ],
\[ 2, 3, 1, 6, 4, 5, 7, 8 ]:
 Order := 24 > |
[ 5, 7, 4, 3, 8, 2, 1, 6 ],
[ 3, 2, 8, 7, 5, 4, 6, 1 ],
[ 4, 7, 6, 1, 8, 3, 2, 5 ]
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
s`BelyiDBBaseFieldData := base_field_data;

/*
Belyi Maps
*/

curves := [* *];
maps := [* *];
K := K1;
X1 := Curve(ProjectiveSpace(PolynomialRing(K1, 2)));
KX1<x> := FunctionField(X1);
phi1 := KX1!(64*x^6/(x^8 + 36*x^6 + 270*x^4 - 972*x^2 + 729));
Append(~curves, X1);
Append(~maps, phi1);
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
