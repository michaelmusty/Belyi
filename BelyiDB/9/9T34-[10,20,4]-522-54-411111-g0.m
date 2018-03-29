s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[10,20,4]-522-54-411111-g0";
s`BelyiDBFilename := "9T34-[10,20,4]-522-54-411111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 10, 20, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 8, 9, 6, 7 ],
[ 7, 5, 2, 3, 4, 8, 9, 1, 6 ],
[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 8, 9, 6, 7 ],
\[ 7, 5, 2, 3, 4, 8, 9, 1, 6 ],
\[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 8, 9, 6, 7 ],
\[ 7, 5, 2, 3, 4, 8, 9, 1, 6 ],
\[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 8, 9, 6, 7 ],
\[ 7, 5, 2, 3, 4, 8, 9, 1, 6 ],
\[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 5, 6, 2, 8, 4, 7, 3, 9, 1 ],
[ 1, 9, 3, 7, 5, 6, 2, 8, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 8, 9, 6, 7 ],
\[ 7, 5, 2, 3, 4, 8, 9, 1, 6 ],
\[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 6, 5, 2, 3, 4, 7, 8, 9, 1 ],
[ 2, 9, 3, 4, 5, 6, 1, 8, 7 ]
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
[ 2, 3, 4, 5, 1, 8, 9, 6, 7 ],
[ 7, 5, 2, 3, 4, 8, 9, 1, 6 ],
[ 2, 8, 3, 4, 5, 6, 7, 9, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 8, 5, 7, 6, 2, 4, 9, 3, 1 ],
[ 6, 9, 5, 8, 2, 4, 3, 1, 7 ],
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
