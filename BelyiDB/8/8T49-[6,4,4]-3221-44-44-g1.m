s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[6,4,4]-3221-44-44-g1";
s`BelyiDBFilename := "8T49-[6,4,4]-3221-44-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 4, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 2;
s`BelyiDBPointedSize := 2;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 7, 8, 6, 4, 1, 3, 5, 2 ],
[ 8, 6, 2, 1, 4, 7, 3, 5 ],
[ 8, 1, 2, 5, 6, 7, 4, 3 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 7, 8, 6, 4, 1, 3, 5, 2 ],
\[ 8, 6, 2, 1, 4, 7, 3, 5 ],
\[ 8, 1, 2, 5, 6, 7, 4, 3 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 7, 8, 6, 4, 1, 3, 5, 2 ],
\[ 8, 6, 2, 1, 4, 7, 3, 5 ],
\[ 8, 1, 2, 5, 6, 7, 4, 3 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 7, 8, 6, 4, 1, 3, 5, 2 ],
\[ 8, 6, 2, 1, 4, 7, 3, 5 ],
\[ 8, 1, 2, 5, 6, 7, 4, 3 ]:
 Order := 20160 > |
[ 3, 7, 1, 6, 2, 4, 5, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 2, 8, 4, 5, 6, 3, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 7, 8, 6, 4, 1, 3, 5, 2 ],
\[ 8, 6, 2, 1, 4, 7, 3, 5 ],
\[ 8, 1, 2, 5, 6, 7, 4, 3 ]:
 Order := 20160 > |
[ 7, 3, 8, 5, 4, 6, 1, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ],
[ 6, 7, 1, 8, 3, 5, 4, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 7, 8, 6, 4, 1, 3, 5, 2 ],
[ 8, 6, 2, 1, 4, 7, 3, 5 ],
[ 8, 1, 2, 5, 6, 7, 4, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 7, 2, 5, 1, 3, 8, 4, 6 ],
[ 6, 5, 4, 1, 7, 3, 8, 2 ],
[ 3, 8, 2, 5, 6, 7, 4, 1 ]
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
