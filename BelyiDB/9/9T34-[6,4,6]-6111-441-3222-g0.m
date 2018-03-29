s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,4,6]-6111-441-3222-g0";
s`BelyiDBFilename := "9T34-[6,4,6]-6111-441-3222-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
\[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
\[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
\[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 2, 8, 6, 4, 3, 7, 5, 9, 1 ],
[ 3, 9, 1, 5, 4, 7, 6, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
\[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 8, 5, 3, 2, 9, 7, 1, 6, 4 ],
[ 8, 7, 4, 3, 9, 2, 6, 1, 5 ]
],
[ PermutationGroup<9 |  
\[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
\[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 4, 9, 3, 2, 8, 7, 5, 6, 1 ],
[ 8, 9, 4, 3, 1, 7, 6, 5, 2 ]
],
[ PermutationGroup<9 |  
\[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
\[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 3, 7, 1, 9, 6, 8, 2, 4 ],
[ 6, 4, 8, 2, 9, 1, 3, 7, 5 ]
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
[ 5, 2, 3, 1, 9, 4, 7, 6, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 3, 1, 2, 5, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 2, 1, 4, 9, 3, 7, 6, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 2, 1, 5, 3, 4, 7, 6, 9, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 3, 2, 7, 6, 4, 8, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 9, 3, 2, 6, 4, 5, 8, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 5, 9, 3, 2, 6, 4, 7, 8, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 9, 3, 2, 5, 4, 8, 6, 7, 1 ]
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
