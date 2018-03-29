s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T20-[4,4,4]-44-44-44-g2";
s`BelyiDBFilename := "8T20-[4,4,4]-44-44-44-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 32 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 6, 3, 8, 1, 2, 7, 4, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |  
\[ 5, 6, 7, 8, 1, 2, 3, 4 ]:
 Order := 2 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 6, 3, 8, 1, 2, 7, 4, 5 ]:
 Order := 32 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 6, 3, 8, 1, 2, 7, 4, 5 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 6, 3, 8, 1, 2, 7, 4, 5 ]:
 Order := 32 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 6, 3, 8, 1, 2, 7, 4, 5 ]:
 Order := 32 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 6, 3, 8, 1, 2, 7, 4, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 8, 5, 6, 7, 4, 1 ],
\[ 7, 4, 1, 6, 3, 8, 5, 2 ],
\[ 6, 3, 8, 1, 2, 7, 4, 5 ]:
 Order := 32 > |
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 32 >) |
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 32 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ],
[ 6, 3, 8, 1, 2, 7, 4, 5 ]
],
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 32 > |
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 1, 6, 7, 4, 5, 2, 3, 8 ],
\[ 2, 3, 8, 5, 6, 7, 4, 1 ]:
 Order := 32 > |
[ 6, 3, 8, 1, 2, 7, 4, 5 ],
[ 2, 3, 8, 5, 6, 7, 4, 1 ],
[ 7, 4, 1, 6, 3, 8, 5, 2 ]
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
