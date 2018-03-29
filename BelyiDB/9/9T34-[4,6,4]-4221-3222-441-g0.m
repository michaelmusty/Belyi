s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[4,6,4]-4221-3222-441-g0";
s`BelyiDBFilename := "9T34-[4,6,4]-4221-3222-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
\[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
\[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
\[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
\[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
\[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
\[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]:
 Order := 362880 > |
[ 4, 1, 2, 3, 6, 5, 8, 7, 9 ],
[ 4, 9, 5, 1, 3, 7, 6, 2, 8 ],
[ 8, 5, 1, 4, 7, 3, 9, 6, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
\[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
\[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]:
 Order := 362880 > |
[ 4, 1, 2, 3, 6, 5, 8, 7, 9 ],
[ 4, 8, 5, 1, 9, 7, 6, 2, 3 ],
[ 8, 9, 1, 4, 7, 3, 2, 6, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
\[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
\[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]:
 Order := 362880 > |
[ 4, 1, 2, 3, 6, 5, 8, 7, 9 ],
[ 4, 8, 5, 1, 3, 7, 9, 2, 6 ],
[ 8, 5, 1, 4, 9, 3, 2, 6, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
\[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
\[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]:
 Order := 362880 > |
[ 4, 1, 2, 3, 6, 5, 8, 7, 9 ],
[ 7, 5, 9, 6, 2, 4, 8, 1, 3 ],
[ 5, 9, 6, 8, 4, 2, 7, 1, 3 ]
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
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
[ 9, 3, 2, 5, 4, 7, 6, 1, 8 ],
[ 5, 8, 3, 2, 7, 4, 9, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
[ 2, 1, 5, 7, 3, 8, 4, 9, 6 ],
[ 7, 2, 1, 5, 9, 3, 6, 4, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
[ 4, 8, 5, 1, 3, 7, 6, 9, 2 ],
[ 1, 4, 9, 5, 7, 3, 2, 6, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 5, 8, 7, 9 ],
[ 9, 8, 5, 7, 6, 3, 4, 2, 1 ],
[ 7, 9, 8, 6, 5, 3, 2, 4, 1 ]
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
