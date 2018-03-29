s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "2T1-[2,2,1]-2-2-11-g0";
s`BelyiDBFilename := "2T1-[2,2,1]-2-2-11-g0.m";
s`BelyiDBDegree := 2;
s`BelyiDBOrders := \[ 2, 2, 1 ];
s`BelyiDBType := "Spherical";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 > |
[ 2, 1 ],
[ 2, 1 ],
[ 1, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 >;
s`BelyiDBMonodromyGroup := PermutationGroup<2 |  
\[ 2, 1 ],
\[ 2, 1 ],
\[ 1, 2 ]:
 Order := 2 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<2 |  
\[ 2, 1 ],
\[ 2, 1 ],
\[ 1, 2 ]:
 Order := 2 >) |
[ PermutationGroup<2 |  
\[ 2, 1 ],
\[ 2, 1 ],
\[ 1, 2 ]:
 Order := 2 > |
[ 2, 1 ],
[ 2, 1 ],
[ 1, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 >) |
[ PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 > |
[ 2, 1 ],
[ 2, 1 ],
[ 1, 2 ]
]
];
s`BelyiDBGaloisOrbits := [ PowerSequence(PowerSequence(PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 >)) |
[ PowerSequence(PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 >) |
[ PermutationGroup<2 |  
\[ 2, 1 ]:
 Order := 2 > |
[ 2, 1 ],
[ 2, 1 ],
[ 1, 2 ]
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
phi1 := KX1!(-1/(x^2 - 1));
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
