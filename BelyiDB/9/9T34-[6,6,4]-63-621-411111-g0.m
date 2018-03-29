s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,4]-63-621-411111-g0";
s`BelyiDBFilename := "9T34-[6,6,4]-63-621-411111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
\[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
\[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
\[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 3, 2, 9, 4, 5, 7, 1, 8 ],
[ 1, 8, 3, 2, 5, 6, 4, 7, 9 ]
],
[ PermutationGroup<9 |  
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
\[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 2, 4, 3, 7, 5, 9, 1, 8 ],
[ 1, 8, 2, 4, 3, 6, 7, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
\[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 6, 3, 2, 4, 7, 5, 9, 1, 8 ],
[ 1, 8, 3, 2, 4, 6, 7, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
\[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
\[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 8, 9, 7 ],
[ 1, 7, 2, 3, 4, 5, 6, 9, 8 ],
[ 7, 1, 3, 4, 5, 6, 8, 2, 9 ]
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
[ 6, 1, 4, 5, 3, 7, 8, 9, 2 ],
[ 3, 2, 9, 5, 4, 1, 6, 7, 8 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 1, 6, 5, 3, 2, 8, 9, 7 ],
[ 8, 2, 6, 1, 4, 3, 9, 7, 5 ],
[ 2, 3, 9, 4, 5, 6, 7, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 4, 8, 6, 5, 3, 7, 1, 9, 2 ],
[ 1, 7, 9, 5, 4, 3, 6, 2, 8 ],
[ 2, 3, 4, 1, 5, 6, 7, 8, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 8, 4, 9, 6, 7, 2, 1, 3 ],
[ 4, 8, 7, 3, 1, 5, 6, 2, 9 ],
[ 2, 3, 9, 4, 5, 6, 7, 8, 1 ]
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
