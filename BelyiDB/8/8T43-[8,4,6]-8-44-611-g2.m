s := BelyiDBInitialize();

/*
Basic Information about the Passport
*/

s`BelyiDBName := "8T43-[8,4,6]-8-44-611-g2";
s`BelyiDBFilename := "8T43-[8,4,6]-8-44-611-g2.m";
s`BelyiDBDegree := 8;
s`BelyiDBOrders := \[ 8, 4, 6 ];
s`BelyiDBType := "Hyperbolic";
s`BelyiDBGenus := 2;
s`BelyiDBSize := 4;
s`BelyiDBPointedSize := 4;
s`BelyiDBPermutationTriple := [ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 8, 7, 2, 5, 6, 3, 1, 4 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ],
[ 3, 6, 2, 5, 1, 4, 7, 8 ]
];
s`BelyiDBAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBPointedAutomorphismGroup := PermutationGroup<8 |   >;
s`BelyiDBMonodromyGroup := PermutationGroup<8 |  
\[ 8, 7, 2, 5, 6, 3, 1, 4 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ]:
 Order := 336 >;
s`BelyiDBPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 8, 7, 2, 5, 6, 3, 1, 4 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 8, 7, 2, 5, 6, 3, 1, 4 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ]:
 Order := 336 > |
[ 7, 3, 6, 8, 4, 5, 2, 1 ],
[ 2, 3, 7, 6, 8, 5, 1, 4 ],
[ 5, 3, 1, 6, 4, 2, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 8, 7, 2, 5, 6, 3, 1, 4 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ]:
 Order := 336 > |
[ 7, 3, 6, 8, 4, 5, 2, 1 ],
[ 6, 7, 2, 3, 1, 8, 4, 5 ],
[ 6, 2, 3, 8, 1, 4, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 8, 7, 2, 5, 6, 3, 1, 4 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ]:
 Order := 336 > |
[ 3, 5, 4, 7, 1, 8, 6, 2 ],
[ 2, 8, 1, 7, 4, 5, 6, 3 ],
[ 6, 2, 3, 8, 1, 4, 5, 7 ]
],
[ PermutationGroup<8 |  
\[ 8, 7, 2, 5, 6, 3, 1, 4 ],
\[ 4, 6, 7, 5, 8, 3, 2, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ]:
 Order := 336 > |
[ 3, 5, 4, 7, 1, 8, 6, 2 ],
[ 4, 3, 1, 2, 7, 5, 8, 6 ],
[ 6, 7, 3, 2, 4, 5, 1, 8 ]
]
];
s`BelyiDBPointedPassport := [ PowerSequence(PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 >) |
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 8, 7, 2, 5, 6, 3, 1, 4 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ],
[ 3, 6, 2, 5, 1, 4, 7, 8 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 7, 8, 6, 1, 2, 5, 4 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ],
[ 4, 2, 8, 5, 3, 1, 7, 6 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 2, 7, 6, 5, 8, 1, 4, 3 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ],
[ 2, 8, 5, 3, 1, 6, 7, 4 ]
],
[ PermutationGroup<8 |  
\[ 2, 3, 4, 5, 6, 8, 7, 1 ],
\[ 3, 6, 2, 5, 1, 4, 7, 8 ],
\[ 6, 3, 2, 5, 4, 1, 8, 7 ]:
 Order := 336 > |
[ 3, 1, 5, 8, 4, 2, 6, 7 ],
[ 4, 6, 7, 5, 8, 3, 2, 1 ],
[ 7, 2, 8, 4, 6, 3, 5, 1 ]
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
