s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[4,4,3]-42111-441-333-g0";
s`BelyiDBFilename := "9T33-[4,4,3]-42111-441-333-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 4, 4, 3 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 7, 5, 4, 8, 1, 6, 2, 9, 3 ],
[ 3, 5, 7, 9, 6, 2, 1, 4, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 7, 5, 4, 8, 1, 6, 2, 9, 3 ],
\[ 3, 5, 7, 9, 6, 2, 1, 4, 8 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 7, 5, 4, 8, 1, 6, 2, 9, 3 ],
\[ 3, 5, 7, 9, 6, 2, 1, 4, 8 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 7, 5, 4, 8, 1, 6, 2, 9, 3 ],
\[ 3, 5, 7, 9, 6, 2, 1, 4, 8 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 7, 6, 4, 9, 5, 1, 2, 3, 8 ],
[ 3, 6, 7, 8, 2, 5, 1, 9, 4 ]
],
[ PermutationGroup<9 |  
\[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
\[ 7, 5, 4, 8, 1, 6, 2, 9, 3 ],
\[ 3, 5, 7, 9, 6, 2, 1, 4, 8 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 8, 6, 3, 7, 9, 4, 2, 5, 1 ],
[ 6, 9, 7, 3, 2, 8, 4, 1, 5 ]
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
[ 7, 5, 4, 8, 1, 6, 2, 9, 3 ],
[ 3, 5, 7, 9, 6, 2, 1, 4, 8 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 3, 4, 1, 6, 5, 7, 8, 9 ],
[ 8, 5, 3, 7, 4, 9, 2, 6, 1 ],
[ 5, 9, 7, 3, 8, 2, 4, 1, 6 ]
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
