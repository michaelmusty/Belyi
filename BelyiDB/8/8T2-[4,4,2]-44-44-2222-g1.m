s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T2-[4,4,2]-44-44-2222-g1";
s`BelyiDBFilename := "8T2-[4,4,2]-44-44-2222-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 2 ];
s`BelyiDBType := "Euclidean";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 8, 1, 2, 7, 4, 5, 6, 3 ],
\[ 7, 4, 5, 2, 3, 8, 1, 6 ]:
 Order := 8 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 4 >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 4, 5, 6, 3, 8, 1, 2, 7 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 8 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 4, 5, 6, 3, 8, 1, 2, 7 ],
[ 5, 6, 7, 8, 1, 2, 3, 4 ]
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
aInvs1 := [ 0, 0, 0, 1, 0 ];
E1 := EllipticCurve(aInvs1);
X1 := BaseChange(E1, K1);
KX1<x,y> := FunctionField(X1);
phi1 := KX1!((-x^4 + 4*x^3 - 6*x^2 + 4*x - 1)/(8*x^3 + 8*x));
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
