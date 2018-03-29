s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T46-[8,8,6]-8-8-3221-g2";
s`BelyiDBFilename := "8T46-[8,8,6]-8-8-3221-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 8, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 7, 4, 5, 3, 8, 1, 2, 6 ],
[ 3, 8, 1, 7, 4, 6, 5, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 7, 4, 5, 3, 8, 1, 2, 6 ],
\[ 3, 8, 1, 7, 4, 6, 5, 2 ]:
 Order := 576 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 7, 4, 5, 3, 8, 1, 2, 6 ],
\[ 3, 8, 1, 7, 4, 6, 5, 2 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 7, 4, 5, 3, 8, 1, 2, 6 ],
\[ 3, 8, 1, 7, 4, 6, 5, 2 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 6, 7, 5, 3, 2, 8, 1, 4 ],
[ 3, 1, 2, 5, 4, 7, 6, 8 ]
],
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 7, 4, 5, 3, 8, 1, 2, 6 ],
\[ 3, 8, 1, 7, 4, 6, 5, 2 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 4, 5, 7, 8, 1, 3, 2, 6 ],
[ 2, 8, 3, 7, 6, 5, 4, 1 ]
],
[ PermutationGroup<8 |  
\[ 6, 4, 5, 8, 1, 2, 3, 7 ],
\[ 7, 4, 5, 3, 8, 1, 2, 6 ],
\[ 3, 8, 1, 7, 4, 6, 5, 2 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 6, 7, 5, 1, 8, 2, 3, 4 ],
[ 3, 1, 2, 6, 7, 4, 5, 8 ]
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
[ 7, 4, 5, 3, 8, 1, 2, 6 ],
[ 3, 8, 1, 7, 4, 6, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 4, 6, 5, 8, 1, 3, 2, 7 ],
[ 3, 2, 8, 7, 6, 5, 4, 1 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 6, 4, 5, 8, 1, 2, 3, 7 ],
[ 4, 7, 6, 3, 1, 2, 8, 5 ],
[ 8, 3, 2, 6, 4, 5, 7, 1 ]
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
