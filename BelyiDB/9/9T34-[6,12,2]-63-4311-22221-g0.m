s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,12,2]-63-4311-22221-g0";
s`BelyiDBFilename := "9T34-[6,12,2]-63-4311-22221-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 12, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
\[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
\[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
\[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 4, 1, 3, 2, 6, 7, 8, 5, 9 ],
[ 5, 2, 4, 3, 1, 8, 9, 6, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
\[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 4, 2, 1, 3, 6, 7, 8, 5, 9 ],
[ 5, 3, 2, 4, 1, 8, 9, 6, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
\[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 2, 1, 8, 5, 4, 6, 7, 3 ],
[ 7, 3, 2, 9, 6, 5, 1, 8, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
\[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
\[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 2, 1, 4, 3, 8, 6, 7, 5 ],
[ 7, 3, 2, 5, 4, 9, 1, 8, 6 ]
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
[ 2, 7, 4, 5, 3, 8, 6, 9, 1 ],
[ 1, 9, 3, 5, 7, 4, 6, 2, 8 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 3, 1, 5, 6, 4, 8, 9, 2 ],
[ 9, 3, 6, 2, 5, 4, 7, 1, 8 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 9, 7, 8 ],
[ 7, 2, 1, 4, 3, 8, 5, 9, 6 ],
[ 9, 3, 2, 5, 4, 7, 6, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 7, 3, 9, 5, 6, 1, 8, 4, 2 ],
[ 9, 6, 8, 2, 5, 4, 7, 1, 3 ],
[ 2, 1, 4, 3, 6, 5, 8, 7, 9 ]
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
