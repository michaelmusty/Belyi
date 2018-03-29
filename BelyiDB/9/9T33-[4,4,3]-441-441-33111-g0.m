s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[4,4,3]-441-441-33111-g0";
s`BelyiDBFilename := "9T33-[4,4,3]-441-441-33111-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
\[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
\[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
\[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 4, 5, 2, 6, 8, 9, 7, 3, 1 ],
[ 1, 9, 3, 8, 5, 2, 4, 7, 6 ]
],
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
\[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 7, 5, 2, 3, 4, 9, 6, 8, 1 ],
[ 5, 9, 3, 4, 8, 2, 7, 1, 6 ]
],
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
\[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 1, 8, 6, 3, 4, 5, 9, 7, 2 ],
[ 5, 1, 9, 4, 2, 6, 3, 8, 7 ]
],
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
\[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 9, 5, 2, 3, 4, 6, 1, 7, 8 ],
[ 5, 7, 3, 4, 9, 2, 6, 8, 1 ]
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
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 2, 5, 6, 3, 7, 9, 1, 8, 4 ],
[ 7, 2, 1, 4, 9, 6, 3, 5, 8 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 2, 8, 6, 3, 4, 5, 1, 7, 9 ],
[ 7, 6, 1, 4, 5, 9, 3, 8, 2 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 3, 2, 9, 7, 4, 5, 6, 1, 8 ],
[ 8, 6, 2, 1, 5, 3, 7, 4, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 9, 1, 6, 3, 4, 5, 7, 2, 8 ],
[ 2, 6, 8, 4, 5, 1, 3, 7, 9 ]
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
