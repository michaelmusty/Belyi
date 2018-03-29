s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[15,3,4]-53-3311-44-g1";
s`BelyiDBFilename := "8T49-[15,3,4]-53-3311-44-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 4, 8, 5, 2, 6, 3, 1, 7 ],
[ 1, 7, 4, 6, 2, 3, 5, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 4, 8, 5, 2, 6, 3, 1, 7 ],
\[ 1, 7, 4, 6, 2, 3, 5, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 4, 8, 5, 2, 6, 3, 1, 7 ],
\[ 1, 7, 4, 6, 2, 3, 5, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 4, 8, 5, 2, 6, 3, 1, 7 ],
\[ 1, 7, 4, 6, 2, 3, 5, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5 ]:
 Order := 20160 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 8, 2, 1, 4, 7, 5, 6, 3 ],
[ 2, 8, 4, 6, 3, 5, 1, 7 ]
],
[ PermutationGroup<8 |  
\[ 4, 8, 5, 2, 6, 3, 1, 7 ],
\[ 1, 7, 4, 6, 2, 3, 5, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5 ]:
 Order := 20160 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 4, 6, 3, 7, 5, 8, 1, 2 ],
[ 8, 3, 1, 5, 7, 4, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 4, 8, 5, 2, 6, 3, 1, 7 ],
\[ 1, 7, 4, 6, 2, 3, 5, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5 ]:
 Order := 20160 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 7, 2, 5, 1, 8, 6, 4, 3 ],
[ 2, 8, 7, 3, 4, 1, 5, 6 ]
],
[ PermutationGroup<8 |  
\[ 4, 8, 5, 2, 6, 3, 1, 7 ],
\[ 1, 7, 4, 6, 2, 3, 5, 8 ],
\[ 2, 3, 4, 1, 6, 7, 8, 5 ]:
 Order := 20160 > |
[ 5, 1, 2, 3, 4, 8, 6, 7 ],
[ 5, 8, 2, 1, 4, 6, 7, 3 ],
[ 3, 8, 5, 1, 4, 7, 2, 6 ]
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
[ 4, 8, 5, 2, 6, 3, 1, 7 ],
[ 1, 7, 4, 6, 2, 3, 5, 8 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 3, 7, 2, 8, 4, 1, 6, 5 ],
[ 5, 6, 3, 1, 4, 8, 7, 2 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 8, 7, 2, 1, 6, 4, 3, 5 ],
[ 7, 6, 3, 4, 1, 8, 5, 2 ],
[ 4, 3, 1, 2, 6, 7, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 3, 8, 4, 2, 7, 5, 6, 1 ],
[ 3, 8, 4, 1, 2, 6, 7, 5 ],
[ 2, 3, 4, 1, 6, 7, 8, 5 ]
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
