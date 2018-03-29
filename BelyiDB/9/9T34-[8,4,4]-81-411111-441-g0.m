s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[8,4,4]-81-411111-441-g0";
s`BelyiDBFilename := "9T34-[8,4,4]-81-411111-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 5, 2, 3, 8, 6, 9, 7, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 8, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 2, 3, 8, 6, 9, 7, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 8, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 2, 3, 8, 6, 9, 7, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 8, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 8, 6, 9, 7, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 8, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 8, 2, 3, 9, 5, 6, 7, 4, 1 ],
[ 1, 9, 2, 3, 8, 5, 6, 7, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 2, 3, 8, 6, 9, 7, 1 ],
\[ 1, 9, 3, 4, 5, 2, 6, 8, 7 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 7, 8, 1, 9 ],
[ 9, 1, 3, 4, 5, 2, 7, 8, 6 ],
[ 8, 2, 6, 3, 4, 5, 9, 7, 1 ]
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
[ 4, 5, 2, 3, 8, 6, 9, 7, 1 ],
[ 1, 9, 3, 4, 5, 2, 6, 8, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 2, 6, 3, 8, 5, 9, 7, 1 ],
[ 1, 9, 2, 4, 5, 6, 3, 8, 7 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
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
