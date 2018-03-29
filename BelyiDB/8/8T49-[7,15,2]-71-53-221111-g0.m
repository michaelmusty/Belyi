s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[7,15,2]-71-53-221111-g0";
s`BelyiDBFilename := "8T49-[7,15,2]-71-53-221111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 7, 15, 2 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 5, 1, 2, 3, 4, 7, 8, 6 ],
[ 6, 2, 3, 4, 5, 1, 8, 7 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8 ],
\[ 5, 1, 2, 3, 4, 7, 8, 6 ],
\[ 6, 2, 3, 4, 5, 1, 8, 7 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8 ],
\[ 5, 1, 2, 3, 4, 7, 8, 6 ],
\[ 6, 2, 3, 4, 5, 1, 8, 7 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8 ],
\[ 5, 1, 2, 3, 4, 7, 8, 6 ],
\[ 6, 2, 3, 4, 5, 1, 8, 7 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 5, 1, 2, 3, 4, 7, 8, 6 ],
[ 6, 2, 3, 4, 5, 1, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8 ],
\[ 5, 1, 2, 3, 4, 7, 8, 6 ],
\[ 6, 2, 3, 4, 5, 1, 8, 7 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 8, 4, 2, 3, 1, 5, 6, 7 ],
[ 8, 5, 3, 4, 2, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8 ],
\[ 5, 1, 2, 3, 4, 7, 8, 6 ],
\[ 6, 2, 3, 4, 5, 1, 8, 7 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 8, 1, 5, 3, 4, 2, 6, 7 ],
[ 8, 2, 6, 4, 5, 3, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 1, 8 ],
\[ 5, 1, 2, 3, 4, 7, 8, 6 ],
\[ 6, 2, 3, 4, 5, 1, 8, 7 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 7, 4, 2, 3, 1, 8, 6, 5 ],
[ 1, 5, 3, 4, 2, 8, 7, 6 ]
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
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 5, 1, 2, 3, 4, 7, 8, 6 ],
[ 6, 2, 3, 4, 5, 1, 8, 7 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 8, 4, 2, 3, 1, 5, 6, 7 ],
[ 8, 5, 3, 4, 2, 6, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 8, 1, 5, 3, 4, 2, 6, 7 ],
[ 8, 2, 6, 4, 5, 3, 7, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 2, 3, 4, 5, 6, 7, 1, 8 ],
[ 7, 4, 2, 3, 1, 8, 6, 5 ],
[ 1, 5, 3, 4, 2, 8, 7, 6 ]
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
