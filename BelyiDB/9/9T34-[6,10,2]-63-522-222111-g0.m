s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,10,2]-63-522-222111-g0";
s`BelyiDBFilename := "9T34-[6,10,2]-63-522-222111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 10, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
\[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
\[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
\[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 8, 4, 3, 2, 5, 6, 7, 1 ],
[ 7, 9, 5, 4, 3, 6, 1, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
\[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 4, 3, 2, 1, 6, 8, 9, 7, 5 ],
[ 5, 4, 3, 2, 1, 9, 7, 8, 6 ]
],
[ PermutationGroup<9 |  
\[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
\[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 1, 4, 3, 2, 7, 6, 5, 8 ],
[ 7, 2, 5, 4, 3, 8, 1, 6, 9 ]
],
[ PermutationGroup<9 |  
\[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
\[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
\[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 9, 1, 2, 3, 8, 7, 6, 5, 4 ],
[ 7, 2, 3, 4, 9, 8, 1, 6, 5 ]
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
[ 3, 1, 4, 6, 2, 5, 8, 9, 7 ],
[ 8, 1, 5, 6, 3, 4, 9, 7, 2 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 9, 5, 8, 6, 3, 7, 4, 1, 2 ],
[ 9, 8, 7, 5, 4, 2, 6, 3, 1 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 3, 5, 6, 2, 4, 7, 8, 9, 1 ],
[ 4, 9, 5, 1, 3, 2, 6, 7, 8 ],
[ 2, 1, 4, 3, 6, 5, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 8, 6, 3, 9, 2, 5, 1, 7 ],
[ 5, 4, 6, 7, 1, 3, 9, 2, 8 ],
[ 9, 3, 2, 5, 4, 6, 7, 8, 1 ]
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
