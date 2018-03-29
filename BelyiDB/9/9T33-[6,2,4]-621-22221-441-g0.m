s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[6,2,4]-621-22221-441-g0";
s`BelyiDBFilename := "9T33-[6,2,4]-621-22221-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 6, 2, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
\[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
\[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
\[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 6, 1, 2, 3, 4, 5, 8, 7, 9 ],
[ 2, 1, 8, 9, 7, 6, 5, 3, 4 ],
[ 1, 8, 9, 7, 6, 2, 3, 5, 4 ]
],
[ PermutationGroup<9 |  
\[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
\[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 6, 1, 2, 3, 4, 5, 8, 7, 9 ],
[ 2, 1, 3, 8, 9, 7, 6, 4, 5 ],
[ 1, 3, 8, 9, 7, 2, 4, 6, 5 ]
],
[ PermutationGroup<9 |  
\[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
\[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 6, 1, 2, 3, 4, 5, 8, 7, 9 ],
[ 3, 7, 1, 5, 4, 9, 2, 8, 6 ],
[ 7, 1, 5, 4, 9, 3, 8, 2, 6 ]
],
[ PermutationGroup<9 |  
\[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
\[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
\[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 6, 1, 2, 3, 4, 5, 8, 7, 9 ],
[ 6, 4, 7, 2, 9, 1, 3, 8, 5 ],
[ 4, 7, 2, 9, 1, 6, 8, 3, 5 ]
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
[ 7, 9, 8, 2, 4, 6, 5, 3, 1 ],
[ 8, 9, 5, 4, 3, 7, 6, 1, 2 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 4, 9, 8, 7, 2, 6, 5, 3, 1 ],
[ 1, 9, 5, 8, 3, 7, 6, 4, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 9, 6, 3, 2, 8, 7, 1, 5, 4 ],
[ 9, 7, 4, 3, 5, 8, 2, 6, 1 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 8, 4, 3, 1, 9, 7, 6, 5 ],
[ 4, 5, 3, 1, 2, 9, 8, 7, 6 ],
[ 2, 4, 1, 3, 6, 7, 8, 5, 9 ]
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
