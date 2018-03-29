s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[12,12,3]-4311-4311-333-g0";
s`BelyiDBFilename := "9T34-[12,12,3]-4311-4311-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 12, 12, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
\[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
\[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
\[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 7, 5, 8, 9 ],
[ 1, 3, 6, 4, 8, 2, 5, 9, 7 ],
[ 4, 1, 6, 2, 9, 7, 3, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
\[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 7, 5, 8, 9 ],
[ 8, 7, 6, 4, 5, 1, 9, 3, 2 ],
[ 4, 6, 9, 8, 2, 5, 3, 1, 7 ]
],
[ PermutationGroup<9 |  
\[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
\[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 7, 5, 8, 9 ],
[ 1, 8, 9, 7, 5, 3, 2, 4, 6 ],
[ 8, 1, 7, 6, 4, 5, 9, 2, 3 ]
],
[ PermutationGroup<9 |  
\[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
\[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
\[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]:
 Order := 362880 > |
[ 2, 3, 4, 1, 6, 7, 5, 8, 9 ],
[ 9, 6, 1, 4, 5, 8, 2, 7, 3 ],
[ 4, 3, 7, 9, 8, 5, 2, 6, 1 ]
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
[ 3, 1, 4, 2, 6, 7, 5, 8, 9 ],
[ 1, 2, 4, 5, 3, 7, 9, 6, 8 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 4, 1, 6, 5, 2, 7, 3, 8 ],
[ 8, 3, 6, 4, 2, 5, 1, 7, 9 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 1, 7, 6, 4, 5, 2, 8, 9 ],
[ 9, 2, 6, 1, 5, 8, 4, 3, 7 ],
[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 2, 9, 1, 7, 5, 6, 8, 4 ],
[ 1, 4, 2, 7, 9, 6, 3, 5, 8 ],
[ 2, 3, 1, 5, 6, 4, 8, 9, 7 ]
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
