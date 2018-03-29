s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T33-[5,3,4]-51111-333-441-g0";
s`BelyiDBFilename := "9T33-[5,3,4]-51111-333-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 5, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 2, 7, 3, 4, 5, 6, 8, 9, 1 ],
[ 4, 9, 1, 3, 7, 5, 6, 2, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 2, 7, 3, 4, 5, 6, 8, 9, 1 ],
\[ 4, 9, 1, 3, 7, 5, 6, 2, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 7, 3, 4, 5, 6, 8, 9, 1 ],
\[ 4, 9, 1, 3, 7, 5, 6, 2, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 >) |
[ PermutationGroup<9 |  
\[ 2, 7, 3, 4, 5, 6, 8, 9, 1 ],
\[ 4, 9, 1, 3, 7, 5, 6, 2, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 5, 1, 2, 3, 4, 6, 7, 8, 9 ],
[ 3, 8, 4, 1, 6, 7, 5, 9, 2 ],
[ 9, 1, 3, 7, 4, 5, 6, 2, 8 ]
],
[ PermutationGroup<9 |  
\[ 2, 7, 3, 4, 5, 6, 8, 9, 1 ],
\[ 4, 9, 1, 3, 7, 5, 6, 2, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]:
 Order := 181440 > |
[ 5, 1, 2, 3, 4, 6, 7, 8, 9 ],
[ 7, 3, 9, 1, 6, 8, 4, 5, 2 ],
[ 9, 2, 7, 8, 4, 5, 1, 6, 3 ]
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
[ 2, 7, 3, 4, 5, 6, 8, 9, 1 ],
[ 4, 9, 1, 3, 7, 5, 6, 2, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5, 9 ]
],
[ PermutationGroup<9 |  
\[ 1, 2, 4, 5, 6, 7, 8, 9, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8, 9 ]:
 Order := 181440 > |
[ 9, 2, 5, 4, 6, 1, 7, 8, 3 ],
[ 4, 6, 2, 9, 8, 3, 5, 7, 1 ],
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
