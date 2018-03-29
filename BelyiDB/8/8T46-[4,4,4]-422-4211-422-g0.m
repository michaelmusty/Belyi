s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T46-[4,4,4]-422-4211-422-g0";
s`BelyiDBFilename := "8T46-[4,4,4]-422-4211-422-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 4, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 1, 8, 5, 4, 6, 7, 2 ],
[ 6, 7, 4, 3, 1, 8, 2, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 3, 1, 8, 5, 4, 6, 7, 2 ],
\[ 6, 7, 4, 3, 1, 8, 2, 5 ]:
 Order := 576 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 3, 1, 8, 5, 4, 6, 7, 2 ],
\[ 6, 7, 4, 3, 1, 8, 2, 5 ]:
 Order := 576 >) |
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 3, 1, 8, 5, 4, 6, 7, 2 ],
\[ 6, 7, 4, 3, 1, 8, 2, 5 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 1, 8, 5, 4, 6, 7, 2 ],
[ 6, 7, 4, 3, 1, 8, 2, 5 ]
],
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 3, 1, 8, 5, 4, 6, 7, 2 ],
\[ 6, 7, 4, 3, 1, 8, 2, 5 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 1, 8, 6, 5, 4, 7, 2 ],
[ 4, 7, 5, 3, 1, 8, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 3, 1, 8, 5, 4, 6, 7, 2 ],
\[ 6, 7, 4, 3, 1, 8, 2, 5 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 8, 1, 2, 6, 5, 4, 7, 3 ],
[ 4, 7, 5, 1, 8, 3, 2, 6 ]
],
[ PermutationGroup<8 |  
\[ 7, 6, 5, 8, 3, 1, 2, 4 ],
\[ 3, 1, 8, 5, 4, 6, 7, 2 ],
\[ 6, 7, 4, 3, 1, 8, 2, 5 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 8, 2, 4, 6, 5, 7, 1 ],
[ 5, 7, 6, 2, 1, 3, 8, 4 ]
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
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 1, 8, 5, 4, 6, 7, 2 ],
[ 6, 7, 4, 3, 1, 8, 2, 5 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 8, 1, 2, 4, 6, 5, 7, 3 ],
[ 5, 7, 6, 1, 8, 3, 2, 4 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 8, 2, 7, 5, 6, 4, 1 ],
[ 6, 4, 5, 2, 1, 3, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 3, 8, 1, 4, 5, 6, 7, 2 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ],
\[ 8, 2, 3, 5, 4, 6, 7, 1 ],
\[ 5, 7, 6, 8, 1, 2, 3, 4 ]:
 Order := 576 > |
[ 7, 6, 5, 8, 3, 1, 2, 4 ],
[ 3, 1, 8, 4, 6, 5, 7, 2 ],
[ 5, 7, 6, 3, 1, 8, 2, 4 ]
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
