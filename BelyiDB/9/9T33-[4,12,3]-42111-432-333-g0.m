s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[4,12,3]-42111-432-333-g0";
s`BelyiDBFilename := "9T33-[4,12,3]-42111-432-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 12, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
\[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
\[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
\[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
\[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 6, 3, 7, 5, 8, 1, 9, 4, 2 ],
[ 8, 6, 9, 2, 1, 4, 3, 5, 7 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
\[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 3, 5, 6, 9, 7, 8, 2, 1, 4 ],
[ 9, 8, 7, 1, 3, 2, 5, 6, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
\[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 8, 7, 1, 9, 4, 3, 2, 6, 5 ],
[ 5, 3, 7, 6, 8, 9, 2, 1, 4 ]
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
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 5, 8, 4, 7, 1, 2, 9, 6, 3 ],
[ 3, 5, 6, 9, 8, 1, 4, 2, 7 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 6, 3, 7, 5, 8, 1, 9, 4, 2 ],
[ 8, 6, 9, 2, 1, 4, 3, 5, 7 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 3, 5, 6, 9, 7, 8, 2, 1, 4 ],
[ 9, 8, 7, 1, 3, 2, 5, 6, 4 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 8, 7, 1, 9, 4, 3, 2, 6, 5 ],
[ 5, 3, 7, 6, 8, 9, 2, 1, 4 ]
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
