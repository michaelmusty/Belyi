s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[6,3,4]-62-3311-4211-g0";
s`BelyiDBFilename := "8T49-[6,3,4]-62-3311-4211-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 3, 4 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 8, 5, 4, 3, 6, 7, 1, 2 ],
[ 3, 7, 8, 4, 5, 2, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 3, 2, 4, 1, 6, 8, 7, 5 ],
[ 2, 1, 3, 8, 5, 4, 6, 7 ]
],
[ PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 2, 7, 4, 6, 5, 3, 1, 8 ],
[ 1, 6, 3, 5, 4, 7, 8, 2 ]
],
[ PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 5, 3, 4, 2, 7, 6, 1, 8 ],
[ 4, 2, 3, 1, 6, 7, 8, 5 ]
],
[ PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 1, 3, 5, 4, 2, 8, 6, 7 ],
[ 5, 2, 4, 3, 7, 1, 6, 8 ]
],
[ PermutationGroup<8 |  
\[ 8, 5, 4, 3, 6, 7, 1, 2 ],
\[ 3, 7, 8, 4, 5, 2, 6, 1 ],
\[ 2, 3, 4, 1, 6, 5, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 4, 2, 7, 6, 5, 1, 8, 3 ],
[ 2, 8, 1, 5, 4, 6, 7, 3 ]
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
[ 8, 5, 4, 3, 6, 7, 1, 2 ],
[ 3, 7, 8, 4, 5, 2, 6, 1 ],
[ 2, 3, 4, 1, 6, 5, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 7, 8, 4, 3, 6, 1, 2, 5 ],
[ 3, 6, 7, 4, 5, 8, 1, 2 ],
[ 2, 3, 4, 1, 6, 5, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 4, 3, 2, 5, 7, 1, 8, 6 ],
[ 1, 6, 3, 2, 8, 4, 5, 7 ],
[ 2, 3, 4, 1, 6, 5, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 3, 8, 2, 7, 6, 1, 4, 5 ],
[ 7, 6, 3, 1, 5, 8, 4, 2 ],
[ 2, 3, 4, 1, 6, 5, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 3, 7, 4, 5, 6, 8, 2, 1 ],
[ 7, 1, 6, 4, 3, 5, 2, 8 ],
[ 8, 1, 2, 5, 4, 6, 7, 3 ]
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
