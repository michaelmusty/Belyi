s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[4,4,3]-441-441-333-g1";
s`BelyiDBFilename := "9T33-[4,4,3]-441-441-333-g1.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 3;
s`BelyiDBPointedSize := 3;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
\[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
\[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
\[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 2, 3, 6, 5, 9, 1, 4, 8, 7 ],
[ 7, 6, 1, 2, 8, 4, 3, 9, 5 ]
],
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
\[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 1, 5, 6, 8, 7, 4, 9, 3, 2 ],
[ 6, 1, 9, 8, 4, 2, 3, 5, 7 ]
],
[ PermutationGroup<9 |  
\[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
\[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
\[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ],
[ 1, 8, 6, 9, 4, 2, 5, 3, 7 ],
[ 5, 1, 6, 8, 2, 7, 3, 9, 4 ]
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
[ 8, 3, 4, 7, 6, 1, 2, 5, 9 ],
[ 6, 8, 7, 2, 3, 9, 5, 4, 1 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 3, 2, 6, 7, 9, 8, 5, 1, 4 ],
[ 8, 7, 2, 1, 9, 5, 3, 4, 6 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 1, 3, 4, 5, 2, 7, 8, 9, 6 ],
[ 8, 2, 9, 7, 1, 5, 3, 6, 4 ],
[ 5, 6, 2, 7, 9, 3, 8, 4, 1 ]
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
