s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T4-[4,2,2]-44-2222-2222-g0";
s`BelyiDBFilename := "8T4-[4,2,2]-44-2222-2222-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 2, 2 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 6, 5, 4, 3, 2, 1, 8, 7 ],
[ 7, 6, 5, 8, 3, 2, 1, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 8, 1, 2, 5, 6, 7, 4, 3 ],
\[ 7, 4, 5, 2, 3, 8, 1, 6 ]:
 Order := 8 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 7, 4, 5, 6, 1 ]:
 Order := 4 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ],
\[ 7, 6, 5, 8, 3, 2, 1, 4 ]:
 Order := 8 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ],
\[ 7, 6, 5, 8, 3, 2, 1, 4 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ],
\[ 7, 6, 5, 8, 3, 2, 1, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 6, 5, 4, 3, 2, 1, 8, 7 ],
[ 7, 6, 5, 8, 3, 2, 1, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 6, 5, 4, 3, 2, 1, 8, 7 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 6, 5, 4, 3, 2, 1, 8, 7 ],
[ 7, 6, 5, 8, 3, 2, 1, 4 ]
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
phi1 := KX1!(-4*x^4/(x^8 - 2*x^4 + 1));
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
