s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T15-[8,8,4]-81-81-441-g2";
s`BelyiDBFilename := "9T15-[8,8,4]-81-81-441-g2.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 8, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]:
 Order := 72 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]:
 Order := 72 >) |
[ PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 8, 2, 6, 9, 3, 1, 4, 7, 5 ],
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ]
],
[ PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 5, 2, 4, 1, 7, 9, 6, 3, 8 ],
[ 1, 5, 4, 8, 9, 2, 3, 7, 6 ]
],
[ PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]:
 Order := 72 > |
[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
[ 8, 2, 6, 9, 3, 1, 4, 7, 5 ],
[ 8, 9, 2, 3, 7, 6, 1, 5, 4 ]
],
[ PermutationGroup<9 |  
\[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
\[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
\[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]:
 Order := 72 > |
[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
[ 5, 2, 4, 1, 7, 9, 6, 3, 8 ],
[ 5, 1, 2, 7, 3, 4, 9, 8, 6 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
[ 1, 6, 7, 3, 2, 9, 8, 4, 5 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
[ 4, 1, 3, 9, 6, 2, 8, 5, 7 ],
[ 9, 8, 6, 5, 1, 2, 7, 3, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 4, 1, 3, 9, 6, 2, 8, 5, 7 ],
[ 7, 1, 8, 2, 5, 9, 3, 6, 4 ],
[ 4, 8, 7, 2, 3, 5, 6, 1, 9 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ]:
 Order := 72 > |
[ 5, 8, 3, 6, 9, 7, 1, 4, 2 ],
[ 2, 8, 1, 7, 4, 6, 3, 9, 5 ],
[ 4, 8, 7, 2, 3, 5, 6, 1, 9 ]
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
