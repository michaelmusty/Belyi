s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T1-[8,8,1]-8-8-11111111-g0";
s`BelyiDBFilename := "8T1-[8,8,1]-8-8-11111111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 1 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 1, 2, 3, 4, 5, 6, 7 ],
[ 1, 2, 3, 4, 5, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 8, 1, 2, 3, 4, 5, 6, 7 ],
\[ 1, 2, 3, 4, 5, 6, 7, 8 ]:
 Order := 8 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 8, 1, 2, 3, 4, 5, 6, 7 ],
\[ 1, 2, 3, 4, 5, 6, 7, 8 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 8, 1, 2, 3, 4, 5, 6, 7 ],
\[ 1, 2, 3, 4, 5, 6, 7, 8 ]:
 Order := 8 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 1, 2, 3, 4, 5, 6, 7 ],
[ 1, 2, 3, 4, 5, 6, 7, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ]:
 Order := 8 > |
[ 2, 3, 4, 5, 6, 7, 8, 1 ],
[ 8, 1, 2, 3, 4, 5, 6, 7 ],
[ 1, 2, 3, 4, 5, 6, 7, 8 ]
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
phi1 := KX1!(-1/(x^8 - 1));
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
