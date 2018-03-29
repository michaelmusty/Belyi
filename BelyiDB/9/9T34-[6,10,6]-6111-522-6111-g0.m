s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,10,6]-6111-522-6111-g0";
s`BelyiDBFilename := "9T34-[6,10,6]-6111-522-6111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 10, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
\[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
\[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
\[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 7, 8, 9 ],
[ 6, 3, 7, 5, 4, 1, 8, 9, 2 ],
[ 9, 2, 5, 4, 1, 6, 3, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
\[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 7, 8, 9 ],
[ 9, 8, 4, 5, 6, 7, 3, 2, 1 ],
[ 8, 7, 3, 4, 5, 9, 6, 2, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
\[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 7, 8, 9 ],
[ 9, 3, 4, 7, 6, 5, 8, 2, 1 ],
[ 8, 2, 3, 6, 5, 9, 4, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
\[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]:
 Order := 362880 > |
[ 6, 1, 2, 3, 4, 5, 7, 8, 9 ],
[ 2, 8, 7, 5, 4, 1, 3, 9, 6 ],
[ 1, 7, 5, 4, 9, 6, 3, 2, 8 ]
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
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 7, 4, 3, 8, 5, 2, 9, 1 ],
[ 1, 9, 7, 4, 3, 6, 2, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 3, 2, 5, 4, 7, 8, 9, 1 ],
[ 1, 9, 3, 2, 5, 4, 6, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 7, 2, 3, 6, 5, 8, 4, 1 ],
[ 5, 9, 3, 4, 8, 6, 2, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 8, 7, 2, 3, 4, 9, 5, 1, 6 ],
[ 9, 8, 3, 4, 5, 7, 2, 1, 6 ]
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
