s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T9-[4,4,2]-441-441-22221-g0";
s`BelyiDBFilename := "9T9-[4,4,2]-441-441-22221-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ]:
 Order := 36 > |
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
[ 5, 4, 9, 2, 1, 6, 8, 7, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
\[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
\[ 5, 4, 9, 2, 1, 6, 8, 7, 3 ]:
 Order := 36 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
\[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
\[ 5, 4, 9, 2, 1, 6, 8, 7, 3 ]:
 Order := 36 >) |
[ PermutationGroup<9 |  
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
\[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
\[ 5, 4, 9, 2, 1, 6, 8, 7, 3 ]:
 Order := 36 > |
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
[ 5, 1, 2, 7, 3, 4, 9, 8, 6 ],
[ 1, 9, 8, 7, 6, 5, 4, 3, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ]:
 Order := 36 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 8, 4, 5, 1, 6, 7, 3, 2, 9 ]:
 Order := 36 > |
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ],
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ],
[ 5, 4, 9, 2, 1, 6, 8, 7, 3 ]
]
];

/*
Base Field Data
*/

base_field_data := [* *];
K1<nu1> := NumberField(Polynomial([RationalField() | 1, 0, 1]));
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
phi1 := KX1!((x^9 + 24*x^8 + 204*x^7 + 648*x^6 + 54*x^5 - 1944*x^4 + 1836*x^3 - 648*x^2 + 81*x)/(x^9 - 57*x^8 + 852*x^7 - 1188*x^6 + 1998*x^5 - 1998*x^4 + 1188*x^3 - 852*x^2 + 57*x - 1));
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
