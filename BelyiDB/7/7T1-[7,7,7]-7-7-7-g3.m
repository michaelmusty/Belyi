s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "7T1-[7,7,7]-7-7-7-g3";
s`BelyiDBFilename := "7T1-[7,7,7]-7-7-7-g3.m";
s`BelyiDBDegree := 7;
s`BelyiDBOrders := \[ 7, 7, 7 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 3;
s`BelyiDBSize := 5;
s`BelyiDBPointedSize := 5;
s`BelyiDBPermutationTriple := [ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 6, 7, 1, 2, 3, 4, 5 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 >;
s`BelyiDBMonodromyGroup := PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 >) |
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 6, 7, 1, 2, 3, 4, 5 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 5, 6, 7, 1, 2, 3, 4 ],
[ 3, 4, 5, 6, 7, 1, 2 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 4, 5, 6, 7, 1, 2, 3 ],
[ 4, 5, 6, 7, 1, 2, 3 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 3, 4, 5, 6, 7, 1, 2 ],
[ 5, 6, 7, 1, 2, 3, 4 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 2, 3, 4, 5, 6, 7, 1 ],
\[ 6, 7, 1, 2, 3, 4, 5 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 6, 7, 1, 2, 3, 4, 5 ],
[ 2, 3, 4, 5, 6, 7, 1 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 >) |
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 6, 7, 1, 2, 3, 4, 5 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 5, 6, 7, 1, 2, 3, 4 ],
[ 3, 4, 5, 6, 7, 1, 2 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 4, 5, 6, 7, 1, 2, 3 ],
[ 4, 5, 6, 7, 1, 2, 3 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 3, 4, 5, 6, 7, 1, 2 ],
[ 5, 6, 7, 1, 2, 3, 4 ]
],
[ PermutationGroup<7 |  
\[ 2, 3, 4, 5, 6, 7, 1 ]:
 Order := 7 > |
[ 2, 3, 4, 5, 6, 7, 1 ],
[ 6, 7, 1, 2, 3, 4, 5 ],
[ 2, 3, 4, 5, 6, 7, 1 ]
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
