s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T46-[8,8,4]-8-8-4211-g2";
s`BelyiDBFilename := "8T46-[8,8,4]-8-8-4211-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 6, 5, 7, 3, 1, 8, 2, 4 ],
[ 2, 1, 3, 7, 4, 5, 6, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 6, 5, 7, 3, 1, 8, 2, 4 ],
\[ 2, 1, 3, 7, 4, 5, 6, 8 ]:
 Order := 576 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 6, 5, 7, 3, 1, 8, 2, 4 ],
\[ 2, 1, 3, 7, 4, 5, 6, 8 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 6, 5, 7, 3, 1, 8, 2, 4 ],
\[ 2, 1, 3, 7, 4, 5, 6, 8 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 7, 4, 6, 8, 3, 1, 2, 5 ],
[ 8, 3, 1, 7, 5, 6, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 6, 5, 7, 3, 1, 8, 2, 4 ],
\[ 2, 1, 3, 7, 4, 5, 6, 8 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 7, 5, 4, 1, 3, 2, 8, 6 ],
[ 2, 8, 1, 6, 5, 4, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 6, 5, 7, 3, 1, 8, 2, 4 ],
\[ 2, 1, 3, 7, 4, 5, 6, 8 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 5, 7, 6, 3, 8, 2, 1, 4 ],
[ 1, 3, 2, 6, 4, 7, 5, 8 ]
],
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 6, 5, 7, 3, 1, 8, 2, 4 ],
\[ 2, 1, 3, 7, 4, 5, 6, 8 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 6, 7, 4, 2, 1, 3, 8, 5 ],
[ 8, 1, 2, 4, 6, 5, 7, 3 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 6, 5, 7, 3, 1, 8, 2, 4 ],
[ 2, 1, 3, 7, 4, 5, 6, 8 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 4, 6, 7, 3, 1, 8, 2, 5 ],
[ 8, 2, 3, 7, 4, 5, 6, 1 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 7, 6, 5, 1, 8, 3, 2, 4 ],
[ 3, 2, 1, 7, 6, 4, 5, 8 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 4, 5, 6, 8, 3, 1, 2, 7 ],
[ 2, 3, 8, 7, 5, 6, 4, 1 ]
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
