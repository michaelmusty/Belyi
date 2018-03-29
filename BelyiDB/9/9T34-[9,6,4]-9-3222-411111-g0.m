s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[9,6,4]-9-3222-411111-g0";
s`BelyiDBFilename := "9T34-[9,6,4]-9-3222-411111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 9, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 1;
s`BelyiDBPointedSize := 1;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 8, 6, 5, 3, 7, 2, 1, 4 ],
[ 9, 8, 7, 5, 4, 3, 6, 2, 1 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 9, 8, 6, 5, 3, 7, 2, 1, 4 ],
\[ 9, 8, 7, 5, 4, 3, 6, 2, 1 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 9, 8, 6, 5, 3, 7, 2, 1, 4 ],
\[ 9, 8, 7, 5, 4, 3, 6, 2, 1 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 9, 8, 6, 5, 3, 7, 2, 1, 4 ],
\[ 9, 8, 7, 5, 4, 3, 6, 2, 1 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 1, 2, 3, 4, 5, 6, 7, 8 ],
[ 8, 3, 2, 5, 4, 7, 6, 9, 1 ],
[ 3, 2, 5, 4, 7, 6, 1, 8, 9 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 8, 6, 5, 3, 7, 2, 1, 4 ],
[ 9, 8, 7, 5, 4, 3, 6, 2, 1 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]
]
];

/*
Base Field Data
*/


/*
Belyi Maps
*/


/*
Powser Bases
*/


/*
Return for eval
*/

return s;
