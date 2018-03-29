s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "9T19-[8,2,4]-81-222111-441-g0";
s`BelyiDBFilename := "9T19-[8,2,4]-81-222111-441-g0.m";
s`BelyiDBDegree := 9;
s`BelyiDBOrders := \[ 8, 2, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 144 > |
[ 7, 5, 2, 6, 4, 1, 8, 3, 9 ],
[ 7, 2, 9, 4, 8, 6, 1, 5, 3 ],
[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<9 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<9 |  
\[ 7, 5, 2, 6, 4, 1, 8, 3, 9 ],
\[ 7, 2, 9, 4, 8, 6, 1, 5, 3 ],
\[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]:
 Order := 144 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 7, 5, 2, 6, 4, 1, 8, 3, 9 ],
\[ 7, 2, 9, 4, 8, 6, 1, 5, 3 ],
\[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]:
 Order := 144 >) |
[ PermutationGroup<9 |  
\[ 7, 5, 2, 6, 4, 1, 8, 3, 9 ],
\[ 7, 2, 9, 4, 8, 6, 1, 5, 3 ],
\[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]:
 Order := 144 > |
[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
[ 1, 9, 4, 3, 5, 6, 8, 7, 2 ],
[ 8, 5, 9, 6, 3, 1, 7, 4, 2 ]
],
[ PermutationGroup<9 |  
\[ 7, 5, 2, 6, 4, 1, 8, 3, 9 ],
\[ 7, 2, 9, 4, 8, 6, 1, 5, 3 ],
\[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]:
 Order := 144 > |
[ 3, 6, 4, 7, 1, 8, 2, 5, 9 ],
[ 1, 6, 8, 4, 9, 2, 7, 3, 5 ],
[ 9, 7, 1, 8, 3, 6, 4, 2, 5 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 144 >) |
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 144 > |
[ 7, 5, 2, 6, 4, 1, 8, 3, 9 ],
[ 7, 2, 9, 4, 8, 6, 1, 5, 3 ],
[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]
],
[ PermutationGroup<9 |  
\[ 2, 9, 4, 5, 3, 7, 8, 6, 1 ],
\[ 4, 5, 6, 7, 8, 9, 1, 2, 3 ],
\[ 6, 3, 8, 5, 2, 4, 1, 7, 9 ],
\[ 2, 1, 5, 4, 3, 7, 6, 8, 9 ]:
 Order := 144 > |
[ 8, 5, 7, 4, 1, 3, 9, 6, 2 ],
[ 1, 2, 7, 8, 6, 5, 3, 4, 9 ],
[ 6, 9, 5, 8, 2, 4, 7, 1, 3 ]
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
