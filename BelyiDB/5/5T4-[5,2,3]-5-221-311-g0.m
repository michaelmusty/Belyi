s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "5T4-[5,2,3]-5-221-311-g0";
s`BelyiDBFilename := "5T4-[5,2,3]-5-221-311-g0.m";
s`BelyiDBDegree := 5;
s`BelyiDBOrders := \[ 5, 2, 3 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<5 |  
\[ 1, 2, 4, 5, 3 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 > |
[ 3, 5, 4, 2, 1 ],
[ 1, 5, 4, 3, 2 ],
[ 2, 3, 1, 4, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<5 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<5 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<5 |  
\[ 3, 5, 4, 2, 1 ],
\[ 1, 5, 4, 3, 2 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<5 |  
\[ 3, 5, 4, 2, 1 ],
\[ 1, 5, 4, 3, 2 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 >) |
[ PermutationGroup<5 |  
\[ 3, 5, 4, 2, 1 ],
\[ 1, 5, 4, 3, 2 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 > |
[ 5, 1, 2, 3, 4 ],
[ 2, 1, 4, 3, 5 ],
[ 1, 4, 3, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<5 |  
\[ 1, 2, 4, 5, 3 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 >) |
[ PermutationGroup<5 |  
\[ 1, 2, 4, 5, 3 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 > |
[ 3, 5, 4, 2, 1 ],
[ 1, 5, 4, 3, 2 ],
[ 2, 3, 1, 4, 5 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<5 |  
\[ 1, 2, 4, 5, 3 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 >)) |
[ PowerSequence(PermutationGroup<5 |  
\[ 1, 2, 4, 5, 3 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 >) |
[ PermutationGroup<5 |  
\[ 1, 2, 4, 5, 3 ],
\[ 2, 3, 1, 4, 5 ]:
 Order := 60 > |
[ 3, 5, 4, 2, 1 ],
[ 1, 5, 4, 3, 2 ],
[ 2, 3, 1, 4, 5 ]
]
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
phi1 := KX1!(-2/9/(x^5 - 10/3*x^4 + 95/18*x^3 - 25/6*x^2 + 25/16*x - 2/9));
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
