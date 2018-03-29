s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[10,12,6]-522-4311-3222-g0";
s`BelyiDBFilename := "9T34-[10,12,6]-522-4311-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 10, 12, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
\[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
\[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
\[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
\[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 8, 3, 2, 5, 4, 9, 6, 1 ],
[ 5, 9, 4, 3, 6, 1, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
\[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 8, 2, 3, 1, 7, 4, 9, 6, 5 ],
[ 9, 4, 2, 3, 6, 5, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
\[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
\[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 6, 2, 1, 7, 9, 3, 5, 8, 4 ],
[ 7, 3, 2, 6, 9, 4, 1, 5, 8 ]
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
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 2, 8, 4, 3, 5, 9, 6, 1 ],
[ 6, 9, 2, 5, 4, 1, 8, 7, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 8, 3, 2, 5, 4, 9, 6, 1 ],
[ 5, 9, 4, 3, 6, 1, 8, 7, 2 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 8, 2, 3, 1, 7, 4, 9, 6, 5 ],
[ 9, 4, 2, 3, 6, 5, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 1, 7, 6, 9, 8 ],
[ 7, 2, 1, 6, 9, 5, 3, 8, 4 ],
[ 6, 3, 2, 7, 9, 1, 4, 5, 8 ]
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
