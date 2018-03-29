s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T14-[4,3,2]-44-3311-2222-g0";
s`BelyiDBFilename := "8T14-[4,3,2]-44-3311-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 3, 2 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 > |
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 1, 3, 8, 6, 5, 7, 4, 2 ],
[ 4, 6, 7, 1, 8, 2, 3, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 1, 3, 8, 6, 5, 7, 4, 2 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 1, 3, 8, 6, 5, 7, 4, 2 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 1, 3, 8, 6, 5, 7, 4, 2 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 > |
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 2, 3, 1, 4, 6, 7, 5, 8 ],
[ 5, 6, 4, 3, 1, 2, 8, 7 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 1, 6, 7, 4, 5, 2 ],
\[ 2, 3, 1, 4, 6, 7, 5, 8 ],
\[ 4, 6, 7, 1, 8, 2, 3, 5 ]:
 Order := 24 > |
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 1, 3, 8, 6, 5, 7, 4, 2 ],
[ 4, 6, 7, 1, 8, 2, 3, 5 ]
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
phi1 := KX1!(6912*x^4/(4096*x^8 + 16384*x^7 + 16384*x^6 + 2048*x^5 + 3968*x^4 - 256*x^3 + 256*x^2 - 32*x + 1));
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
