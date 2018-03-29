s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T50-[15,4,6]-53-422-332-g1";
s`BelyiDBFilename := "8T50-[15,4,6]-53-422-332-g1.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 15, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 1;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 6, 8, 2, 7, 4, 3, 1 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 3, 8, 5, 4, 1, 6, 2 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 7, 1, 6, 8, 4, 5, 2 ],
[ 7, 3, 8, 1, 6, 5, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 2, 4, 6, 8, 7, 3, 5, 1 ],
[ 7, 8, 1, 6, 2, 4, 3, 5 ]
],
[ PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 2, 3, 8, 7, 6, 5, 4, 1 ],
[ 6, 8, 1, 2, 7, 3, 5, 4 ]
],
[ PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 7, 1, 8, 6, 5, 4, 2 ],
[ 6, 3, 8, 1, 7, 4, 5, 2 ]
],
[ PermutationGroup<8 |  
\[ 5, 6, 8, 2, 7, 4, 3, 1 ],
\[ 2, 3, 4, 1, 6, 5, 8, 7 ],
\[ 7, 3, 8, 5, 4, 1, 6, 2 ]:
 Order := 40320 > |
[ 2, 3, 4, 5, 1, 7, 8, 6 ],
[ 3, 7, 4, 8, 6, 5, 2, 1 ],
[ 6, 8, 7, 1, 3, 4, 5, 2 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 6, 8, 2, 7, 4, 3, 1 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 7, 3, 8, 5, 4, 1, 6, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 5, 7, 4, 6, 3, 1, 8, 2 ],
[ 2, 3, 8, 5, 4, 7, 6, 1 ],
[ 7, 3, 4, 2, 8, 5, 1, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 7, 5, 8, 1, 4, 3, 2, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 8, 5, 6, 1, 7, 4, 2 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 2, 8, 5, 1, 7, 4, 3, 6 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 4, 8, 5, 2, 7, 6, 1 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 7, 8, 1 ],
\[ 2, 1, 3, 4, 5, 6, 7, 8 ]:
 Order := 40320 > |
[ 6, 5, 8, 1, 7, 3, 2, 4 ],
[ 2, 3, 4, 1, 6, 5, 8, 7 ],
[ 3, 8, 5, 7, 1, 4, 6, 2 ]
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
