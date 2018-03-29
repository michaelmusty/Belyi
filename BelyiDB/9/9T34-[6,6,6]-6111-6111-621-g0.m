s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T34-[6,6,6]-6111-6111-621-g0";
s`BelyiDBFilename := "9T34-[6,6,6]-6111-6111-621-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 6, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
\[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]:
 Order := 362880 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
\[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]:
 Order := 362880 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
\[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
\[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 2, 3, 4, 8, 7, 5, 9, 1 ],
[ 1, 9, 2, 3, 4, 7, 6, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
\[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 2, 3, 7, 5, 4, 8, 9, 1 ],
[ 1, 9, 2, 3, 6, 5, 4, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
\[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
\[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 2, 3, 7, 4, 6, 8, 9, 1 ],
[ 6, 9, 2, 3, 5, 1, 4, 7, 8 ]
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
[ 9, 2, 3, 4, 7, 5, 8, 1, 6 ],
[ 9, 8, 2, 3, 4, 6, 5, 7, 1 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 2, 3, 4, 8, 7, 5, 9, 1 ],
[ 1, 9, 2, 3, 4, 7, 6, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 6, 2, 3, 7, 5, 4, 8, 9, 1 ],
[ 1, 9, 2, 3, 6, 5, 4, 7, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 5, 6, 7, 8, 9, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8, 9 ]:
 Order := 362880 > |
[ 2, 3, 4, 5, 6, 1, 7, 8, 9 ],
[ 5, 2, 3, 7, 4, 6, 8, 9, 1 ],
[ 6, 9, 2, 3, 5, 1, 4, 7, 8 ]
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
