s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T49-[6,3,5]-62-3311-5111-g0";
s`BelyiDBFilename := "8T49-[6,3,5]-62-3311-5111-g0.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 6, 3, 5 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 0;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 5, 7, 4, 3, 6, 2, 8, 1 ],
[ 1, 8, 6, 4, 3, 5, 2, 7 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 >) |
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 1, 3, 8, 5, 6, 4, 7, 2 ],
[ 8, 2, 6, 4, 5, 1, 3, 7 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 5, 2, 7, 4, 6, 1, 8, 3 ],
[ 2, 8, 4, 1, 5, 6, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 5, 7, 3, 4, 6, 1, 8, 2 ],
[ 8, 3, 4, 1, 5, 6, 7, 2 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 5, 2, 3, 7, 6, 1, 8, 4 ],
[ 2, 3, 8, 1, 5, 6, 7, 4 ]
],
[ PermutationGroup<8 |  
\[ 5, 7, 4, 3, 6, 2, 8, 1 ],
\[ 1, 8, 6, 4, 3, 5, 2, 7 ],
\[ 2, 3, 4, 5, 1, 6, 7, 8 ]:
 Order := 20160 > |
[ 6, 1, 2, 3, 4, 5, 8, 7 ],
[ 2, 3, 1, 5, 8, 6, 7, 4 ],
[ 1, 2, 8, 4, 6, 3, 5, 7 ]
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
[ 5, 7, 4, 3, 6, 2, 8, 1 ],
[ 1, 8, 6, 4, 3, 5, 2, 7 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 4, 7, 5, 3, 6, 8, 2, 1 ],
[ 7, 1, 6, 4, 3, 5, 2, 8 ],
[ 8, 1, 4, 2, 5, 6, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 4, 7, 8, 3, 6, 1, 2, 5 ],
[ 7, 1, 3, 4, 8, 5, 2, 6 ],
[ 8, 1, 4, 2, 5, 6, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 4, 7, 8, 5, 6, 3, 2, 1 ],
[ 7, 1, 3, 6, 4, 5, 2, 8 ],
[ 8, 1, 4, 2, 5, 6, 7, 3 ]
],
[ PermutationGroup<8 |  
\[ 2, 1, 4, 5, 6, 7, 8, 3 ],
\[ 2, 3, 1, 4, 5, 6, 7, 8 ]:
 Order := 20160 > |
[ 8, 6, 2, 5, 4, 7, 1, 3 ],
[ 4, 7, 3, 8, 5, 2, 6, 1 ],
[ 2, 3, 4, 5, 1, 6, 7, 8 ]
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
