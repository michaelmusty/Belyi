s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T1-[9,9,1]-9-9-111111111-g0";
s`BelyiDBFilename := "9T1-[9,9,1]-9-9-111111111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 9, 1 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
\[ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 9 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
\[ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 9 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
\[ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ]:
 Order := 9 > |
[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 1, 2, 3, 4, 5, 6, 7, 8, 9 ]
]
];

/*
Base Field Data
*/

base_field_data := [* *];
K1<nu1> := RationalsAsNumberField();
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
phi1 := KX1!(x^9/(x^9 - 1));
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
