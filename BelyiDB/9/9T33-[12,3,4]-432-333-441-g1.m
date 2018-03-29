s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[12,3,4]-432-333-441-g1";
s`BelyiDBFilename := "9T33-[12,3,4]-432-333-441-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 12, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 181440 > |
[ 4, 1, 2, 3, 7, 5, 6, 9, 8 ],
[ 5, 3, 9, 8, 7, 4, 1, 6, 2 ],
[ 9, 2, 6, 7, 8, 5, 1, 3, 4 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 181440 > |
[ 4, 1, 2, 3, 7, 5, 6, 9, 8 ],
[ 5, 3, 9, 7, 8, 4, 6, 1, 2 ],
[ 9, 2, 6, 8, 7, 4, 1, 3, 5 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 181440 > |
[ 4, 1, 2, 3, 7, 5, 6, 9, 8 ],
[ 7, 6, 1, 2, 8, 4, 3, 9, 5 ],
[ 4, 7, 6, 3, 2, 1, 9, 8, 5 ]
],
[ PermutationGroup<9 |  
\[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
\[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
\[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]:
 Order := 181440 > |
[ 4, 1, 2, 3, 7, 5, 6, 9, 8 ],
[ 7, 9, 2, 1, 8, 5, 4, 6, 3 ],
[ 3, 9, 7, 4, 8, 1, 6, 2, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 5, 9, 6, 2, 8, 3, 1, 7 ],
[ 3, 8, 5, 9, 1, 2, 4, 6, 7 ],
[ 2, 3, 9, 5, 6, 7, 4, 8, 1 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 9, 4, 8, 6, 1, 2, 5, 3, 7 ],
[ 8, 5, 2, 6, 3, 7, 4, 9, 1 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 4, 8, 5, 1, 3, 9, 6, 7 ],
[ 6, 5, 2, 1, 3, 4, 8, 9, 7 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 7, 3, 5, 9, 2, 8, 4, 6, 1 ],
[ 7, 9, 5, 2, 6, 3, 8, 1, 4 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
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
